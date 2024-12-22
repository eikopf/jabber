//! Implementation of module-local name resolution.

use std::{collections::HashMap, num::NonZeroUsize};

use crate::{
    ast::{
        bound as ast,
        common::{Qualifier, ViSp, Vis},
        unbound_lowered as ubd,
    },
    literal,
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
};

use super::{
    import_res::ImportResEnv, Env, Loc, ModId, Name, Res, ResError, ResWarning,
    Term, TermId, Type, TypeId,
};

/// The type of names in the resolved tree, which may either be a [`ast::Bound`]
/// value or unresolved spanned symbols.
pub type BoundResult = Result<ast::Bound, Spanned<ast::NameContent>>;

fn bound_result_span(res: &BoundResult) -> Span {
    match res {
        Ok(bound) => bound.span(),
        Err(Spanned { span, .. }) => *span,
    }
}

/// The environment type produced by [`resolve`].
pub type ResEnv = Env<
    Spanned<ast::Term<BoundResult>>,
    Spanned<ast::Type<BoundResult>>,
    HashMap<Symbol, ViSp<Res>>,
>;

#[derive(Debug, Clone)]
struct Scope<T> {
    kind: ScopeKind,
    bindings: HashMap<Symbol, T>,
}

impl<T: Copy> Scope<T> {
    fn get(&self, symbol: Symbol) -> Option<T> {
        self.bindings.get(&symbol).copied()
    }
}

impl<T> Scope<T> {
    fn insert(&mut self, key: Symbol, value: T) {
        let __prev = self.bindings.insert(key, value);
        // we should never have to overwrite any binding
        debug_assert!(__prev.is_none());
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ScopeKind {
    /// The scope introduced by a type expression.
    Type,
    /// The scope introduced by the generic parameters in type declarations.
    TypeDeclParams,
    /// The scope introduced by the parameters in `fn` declarations.
    FnDeclParams,
    /// The scope introduced by the parameters of a lambda expression.
    LambdaParams,
    /// The scope introduced by an individual match arm.
    MatchArm,
    /// The scope introduced by a block expression.
    Block,
    /// The scope introduced by a `let` statement within a block.
    LetStmt,
}

#[derive(Debug, Clone, Copy)]
pub struct Binding {
    pub ident: Spanned<Symbol>,
    pub id: ast::BindingId,
}

impl From<Binding> for ast::Bound {
    fn from(value: Binding) -> Self {
        value.id.with_ident(value.ident)
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ScopeName {
    Root(Res),
    Scoped(Binding),
}

impl ScopeName {
    pub fn id(&self) -> ast::BindingId {
        match self {
            ScopeName::Root(res) => ast::BindingId::Global(*res),
            ScopeName::Scoped(Binding { id, .. }) => *id,
        }
    }
}

#[derive(Debug, Clone)]
pub enum LocalResError {
    DuplicateGenericTypeParams {
        module: ModId,
        ty: TypeId,
        first: Spanned<Symbol>,
        second: Spanned<Symbol>,
    },
    UsedSuperInRootModule {
        module: ModId,
        path: Spanned<ast::Path>,
        super_span: Span,
    },
    /// An error produced when resolving a local (i.e. non-import) path
    Path {
        module: ModId,
        error: LocalPathResError,
        path: Spanned<ast::Path>,
    },
    DuplicateRecordFieldName {
        module: ModId,
        ty: TypeId,
        first: Spanned<Symbol>,
        second: Spanned<Symbol>,
    },
    StringLiteralError {
        module: ModId,
        error: literal::StringLiteralError,
    },
    CharLiteralError {
        module: ModId,
        error: literal::CharLiteralError,
    },
    IntLiteralOverflowError {
        module: ModId,
        error: literal::IntLiteralOverflowError,
    },
    TupleFieldOverflowError {
        module: ModId,
        span: Span,
    },
    NotARecordConstr {
        module: ModId,
        name: Spanned<ast::NameContent>,
    },
    NoSuchRecordExprField {
        module: ModId,
        constr: (TypeId, Symbol),
        field: Spanned<Symbol>,
    },
}

#[derive(Debug, Clone)]
pub enum LocalPathResError {
    /// The first element of the path is a locally-bound value.
    StartsWithLocalBinding(ast::LocalBinding),
    /// A path element does not exist.
    ElementDne(Spanned<Symbol>),
    /// A path element exists, but is not externally visible.
    Private(ast::Name<Res>),
    /// A term appeared with trailing elements.
    NonTerminalTerm {
        term: ast::Name<TermId>,
        tail: Box<[Spanned<Symbol>]>,
    },
    /// A type constructor was addressed but does not exist.
    TypeConstrDne {
        ty: ast::Name<TypeId>,
        constr: Spanned<Symbol>,
    },
    /// The path tries to access a constructor of an extern type.
    TypeConstrOfExternType {
        ty: ast::Name<TypeId>,
        constr: Spanned<Symbol>,
    },
    /// The path tries to access a constructor of a type alias.
    TypeConstrOfTypeAlias {
        ty: ast::Name<TypeId>,
        constr: Spanned<Symbol>,
    },
    /// The path tries to access a constructor of an opaque ADT.
    TypeConstrOfOpaqueAdt {
        ty: ast::Name<TypeId>,
        constr: Spanned<Symbol>,
    },
    /// The path tries to access an element "within" a type constructor.
    TooManyElementsAfterType {
        ty: ast::Name<TypeId>,
        /// INVARIANT: this list contains at least two elements.
        tail: Box<[Spanned<Symbol>]>,
    },
}

#[derive(Debug, Clone)]
pub enum LocalResWarning {
    ShadowedName {
        module: ModId,
        shadowed: ScopeName,
        shadower: Spanned<Symbol>,
    },
}

const INITIAL_SCOPE_DEPTH_CAPACITY: usize = 4;
const INITIAL_SCOPE_BINDING_CAPACITY: usize = 6;

/// A module-local resolver.
#[derive(Debug)]
struct Resolver<'a> {
    /// A environment with the `types` and `terms` fields probably invalid. We
    /// take a mutable reference to get mutable access to the interner, but
    /// otherwise don't write through this field.
    env: &'a mut ResEnv,
    stale_types: &'a [Type<Spanned<ubd::SymType>>],
    warnings: &'a mut Vec<ResWarning>,
    errors: &'a mut Vec<ResError>,
    module: ModId,
    /// The ID of the item currently being resolved.
    id: Res,
    scopes: Vec<Scope<Binding>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Operator {
    Defined(TermId),
    LazyAnd,
    LazyOr,
    Mutate,
}

impl Operator {
    fn with_operands(
        self,
        operator_content: Spanned<Symbol>,
        operands: SpanSeq<ast::Expr<BoundResult>>,
    ) -> ast::Expr<BoundResult> {
        match self {
            Operator::Defined(term_id) => {
                let callee = Box::new(operator_content.span.with(
                    ast::Expr::Name(Ok(ast::Bound::from(ast::Name {
                        content: operator_content,
                        id: Res::Term(term_id),
                    }))),
                ));

                let kind = match operands.len() {
                    1 => ast::CallExprKind::DesugaredPrefixOp,
                    2 => ast::CallExprKind::DesugaredBinaryOp,
                    n => {
                        panic!("tried to desugar operator with {} operands", n)
                    }
                };

                ast::Expr::Call {
                    callee,
                    kind,
                    args: operands,
                }
            }
            Operator::LazyAnd => {
                assert!(operands.len() == 2);

                let operator = operator_content.span;
                let lhs = Box::new(operands[0].clone());
                let rhs = Box::new(operands[1].clone());

                ast::Expr::LazyAnd { operator, lhs, rhs }
            }
            Operator::LazyOr => {
                assert!(operands.len() == 2);

                let operator = operator_content.span;
                let lhs = Box::new(operands[0].clone());
                let rhs = Box::new(operands[1].clone());

                ast::Expr::LazyOr { operator, lhs, rhs }
            }
            Operator::Mutate => {
                assert!(operands.len() == 2);

                let operator = operator_content.span;
                let lhs = Box::new(operands[0].clone());
                let rhs = Box::new(operands[1].clone());

                ast::Expr::Mutate { operator, lhs, rhs }
            }
        }
    }
}

/// Helper macro for retrieving operator [`TermId`] values at runtime.
macro_rules! core_operator {
    ($resolver:expr, $module:expr, $item:expr, $op:expr) => {{
        let module_name = $resolver.env.interner.intern_static($module);
        let item_name = $resolver.env.interner.intern_static($item);
        let op_symbol = $resolver.env.interner.intern_static($op);

        let module = $resolver
            .env
            .magic_core_submodule(module_name)
            .expect(concat!("core.", stringify!($module), " exists"));

        let op = Operator::Defined(
            $resolver
                .env
                .item_in_module(item_name, module)
                .and_then(Res::as_term)
                .expect(concat!(
                    "core.",
                    stringify!($module),
                    ".",
                    stringify!($item),
                    " exists"
                )),
        );

        (op, op_symbol)
    }};
}

impl<'a> Resolver<'a> {
    // UTILITY METHODS

    fn new(
        env: &'a mut ResEnv,
        stale_types: &'a [Type<Spanned<ubd::SymType>>],
        warnings: &'a mut Vec<ResWarning>,
        errors: &'a mut Vec<ResError>,
        module: ModId,
        id: Res,
    ) -> Self {
        Self {
            env,
            stale_types,
            warnings,
            errors,
            module,
            id,
            scopes: Vec::with_capacity(INITIAL_SCOPE_DEPTH_CAPACITY),
        }
    }

    /// API wrapper over UID creation in case this later requires mutable
    /// access to a field in `self`.
    fn fresh(&mut self) -> crate::unique::Uid {
        crate::unique::Uid::fresh()
    }

    fn fresh_local(&mut self, ident: Spanned<Symbol>) -> Binding {
        Binding {
            ident,
            id: ast::BindingId::Local(self.fresh()),
        }
    }

    fn intern_ident_in_module(
        &mut self,
        Spanned { span, .. }: Spanned<ubd::ast::Ident>,
        module: ModId,
    ) -> Spanned<Symbol> {
        span.with(self.env.intern_source_span_in_module(module, span).unwrap())
    }

    fn intern_path(
        &mut self,
        span: Span,
        qualifier: Option<Spanned<Qualifier>>,
        elements: &[Spanned<ubd::ast::Ident>],
    ) -> Spanned<ast::Path> {
        span.with(ast::Path {
            qualifier,
            elements: elements
                .iter()
                .map(|ident| self.intern_ident_in_module(*ident, self.module))
                .collect(),
        })
    }

    fn get_spanned_str(&self, span: Span) -> &str {
        let file = self.env.get_module(self.module).file;
        let file = self.env.get_file_ref(file);

        span.in_source(file.contents().as_bytes())
            .expect("source spans always point to UTF-8 byte sequences")
    }

    fn emit_local_error(&mut self, error: LocalResError) {
        let package = self.env.get_module(self.module).package;
        self.errors.push(ResError::LocalRes { package, error })
    }

    fn get_stale_type(&self, id: TypeId) -> &Type<Spanned<ubd::SymType>> {
        self.stale_types
            .get(id.0)
            .expect("Type IDs are valid by construction")
    }

    fn enter_new_scope(&mut self, kind: ScopeKind) {
        self.scopes.push(Scope {
            kind,
            bindings: HashMap::with_capacity(INITIAL_SCOPE_BINDING_CAPACITY),
        });
    }

    /// Pops the topmost scope off the stack and returns it.
    fn leave_scope(&mut self) -> Option<Scope<Binding>> {
        self.scopes.pop()
    }

    /// Leaves the enclosing block scope by popping scopes off the stack
    /// up to and including the topmost [`ScopeKind::Block`] scope. Returns
    /// the number of scopes removed as a sanity check, which will be [`None`]
    /// if there was no enclosing block scope.
    fn leave_block_scope(&mut self) -> Option<NonZeroUsize> {
        let depth = self
            .scopes
            .iter()
            .rev()
            .position(|s| s.kind == ScopeKind::Block);

        depth.map(|n| {
            let pop_count = unsafe { NonZeroUsize::new_unchecked(n + 1) };
            self.scopes.truncate(self.scopes.len() - n - 1);
            pop_count
        })
    }

    fn scope_kind(&self) -> Option<ScopeKind> {
        self.scopes.last().map(|Scope { kind, .. }| kind).copied()
    }

    /// Returns the depth of the scope stack. A value of `0` denotes the module
    /// root scope.
    fn depth(&self) -> usize {
        self.scopes.len()
    }

    fn in_root_scope(&self) -> bool {
        self.depth() == 0
    }

    fn get_in_root_scope(&self, symbol: Symbol) -> Option<Res> {
        self.env
            .get_module(self.module)
            .items
            .get(&symbol)
            .copied()
            .map(Vis::unwrap)
            .map(Spanned::unwrap)
    }

    fn lookup(&self, symbol: Symbol) -> Option<ScopeName> {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(symbol))
            .map(ScopeName::Scoped)
            .or_else(|| self.get_in_root_scope(symbol).map(ScopeName::Root))
    }

    fn nearest_shadowed_name(&self, symbol: Symbol) -> Option<ScopeName> {
        self.scopes
            .iter()
            .rev()
            .skip(1) // skip the innermost scope
            .find_map(|scope| scope.get(symbol))
            .map(ScopeName::Scoped)
            .or_else(|| self.get_in_root_scope(symbol).map(ScopeName::Root))
    }

    fn check_name_shadowing(&mut self, shadower: Spanned<Symbol>) {
        if let Some(shadowed) = self.nearest_shadowed_name(shadower.item) {
            let warning = LocalResWarning::ShadowedName {
                module: self.module,
                shadowed,
                shadower,
            };

            let package = self.env.get_module(self.module).package;
            self.warnings
                .push(ResWarning::LocalRes { package, warning });
        }
    }

    /// Inserts the given binding into the current topmost scope.
    ///
    /// # Panics
    /// Panics if `self.scopes` is empty.
    fn insert(&mut self, binding: Binding) {
        assert!(!self.in_root_scope());
        let symbol = binding.ident;
        self.check_name_shadowing(symbol);

        let scope = self.scopes.last_mut().unwrap();
        scope.insert(*symbol, binding);
    }

    fn bind_global_with_symbol(
        &self,
        Loc { item: ident, .. }: Name,
        id: Res,
    ) -> ast::GlobalBinding {
        ast::GlobalBinding { content: ident, id }
    }

    fn bind_global_with_ident(
        &mut self,
        ident: Spanned<ubd::ast::Ident>,
        id: Res,
    ) -> ast::GlobalBinding {
        ast::GlobalBinding {
            content: self.intern_ident_in_module(ident, self.module),
            id,
        }
    }

    // TYPE VISITORS

    fn visit_type(
        &mut self,
        Spanned { item: ty, span }: Spanned<ubd::SymType>,
    ) -> Spanned<ast::Type<BoundResult>> {
        span.with(match ty {
            ubd::Type::Adt(adt) => {
                ast::Type::Adt(self.visit_adt(span.with(adt)).unwrap())
            }
            ubd::Type::Alias(type_alias) => ast::Type::Alias(
                self.visit_type_alias(span.with(type_alias)).unwrap(),
            ),
            ubd::Type::Extern(extern_type) => ast::Type::Extern(
                self.visit_extern_type(span.with(extern_type)).unwrap(),
            ),
        })
    }

    fn visit_adt(
        &mut self,
        Spanned {
            item:
                ubd::Adt {
                    name,
                    opacity,
                    params,
                    constructors,
                },
            span,
        }: Spanned<ubd::SymAdt>,
    ) -> Spanned<ast::Adt<BoundResult>> {
        // annotate name
        let name = self.bind_global_with_symbol(name, self.id);

        // process params, potentially emitting some warnings
        self.enter_new_scope(ScopeKind::TypeDeclParams);
        let params = self.visit_generic_params(params);

        let constructors = constructors
            .into_iter()
            .map(|(name, constr)| (name, self.visit_type_constructor(constr)))
            .collect();

        span.with(ast::Adt {
            name,
            opacity,
            params,
            constructors,
        })
    }

    fn visit_type_constructor(
        &mut self,
        Spanned {
            item:
                ubd::ast::TyConstr {
                    doc_comment: _,
                    attributes: _,
                    name,
                    payload,
                },
            span,
        }: Spanned<ubd::ast::TyConstr>,
    ) -> Spanned<ast::TyConstr<BoundResult>> {
        let name = self.intern_ident_in_module(name, self.module);
        let ty = self
            .id
            .as_type()
            .expect("Only types have type constructors to visit");

        let payload = payload.map(|Spanned { item, span }| match item {
            ubd::ast::TyConstrPayload::Tuple(unbound_tys) => {
                // SANITY CHECK: `unbound_tys` cannot be empty
                debug_assert!(!unbound_tys.is_empty());

                let mut tys = Vec::with_capacity(unbound_tys.len());

                for ty in unbound_tys {
                    let ty = self.visit_ty(ty);
                    tys.push(ty);
                }

                span.with(ast::TyConstrPayload::Tuple(tys.into_boxed_slice()))
            }
            ubd::ast::TyConstrPayload::Record(unbound_fields) => {
                if unbound_fields.is_empty() {
                    todo!("emit warning; this should be a unit constr!");
                }

                let mut fields =
                    HashMap::<_, Spanned<ast::RecordField<_>>>::with_capacity(
                        unbound_fields.len(),
                    );

                for field in unbound_fields {
                    let (name, field) = self.visit_record_field(field);

                    match fields.get(&name) {
                        // found a record field with the same name!
                        Some(conflict) => {
                            self.emit_local_error(
                                LocalResError::DuplicateRecordFieldName {
                                    module: self.module,
                                    ty,
                                    first: conflict.item().name,
                                    second: field.name,
                                },
                            );
                        }
                        // otherwise just insert it and move on
                        None => {
                            fields.insert(name, field);
                        }
                    }
                }

                span.with(ast::TyConstrPayload::Record(fields))
            }
        });

        span.with(ast::TyConstr { name, ty, payload })
    }

    fn visit_record_field(
        &mut self,
        Spanned {
            item:
                ubd::ast::RecordField {
                    doc_comment: _,
                    attributes: _,
                    mutability,
                    name,
                    ty,
                },
            span,
        }: Spanned<ubd::ast::RecordField>,
    ) -> (Symbol, Spanned<ast::RecordField<BoundResult>>) {
        let mutability = match mutability {
            ubd::ast::Mutability::Immut => None,
            ubd::ast::Mutability::Mut(span) => Some(span),
        };

        let name = self.intern_ident_in_module(name, self.module);
        let ty = self.visit_ty(ty);

        (
            *name,
            span.with(ast::RecordField {
                mutability,
                name,
                ty,
            }),
        )
    }

    fn visit_type_alias(
        &mut self,
        Spanned {
            item: ubd::TypeAlias { name, params, ty },
            span,
        }: Spanned<ubd::SymTypeAlias>,
    ) -> Spanned<ast::TypeAlias<BoundResult>> {
        // annotate name
        let name = self.bind_global_with_symbol(name, self.id);

        // process params, potentially emitting some warnings
        self.enter_new_scope(ScopeKind::TypeDeclParams);
        let params = self.visit_generic_params(params);

        // process alias rhs
        let ty = self.visit_ty(ty);

        span.with(ast::TypeAlias { name, params, ty })
    }

    fn visit_extern_type(
        &mut self,
        Spanned {
            item: ubd::ExternType { name, params },
            span,
        }: Spanned<ubd::SymExternType>,
    ) -> Spanned<ast::ExternType> {
        // annotate name
        let name = self.bind_global_with_symbol(name, self.id);

        // process params, potentially emitting some warnings
        self.enter_new_scope(ScopeKind::TypeDeclParams);
        let params = self.visit_generic_params(params);

        // return the spanned & processed extern type
        span.with(ast::ExternType { name, params })
    }

    /// Visits the `params` field common to all type declarations, checking
    /// for uniqueness and shadowing of names in the module root scope.
    fn visit_generic_params(
        &mut self,
        params: Box<[Name]>,
    ) -> Box<[ast::LocalBinding]> {
        // DEBUG MODE SANITY CHECKS
        debug_assert_eq!(self.depth(), 1); // is this is too restrictive?
        debug_assert_eq!(self.scope_kind(), Some(ScopeKind::TypeDeclParams));
        debug_assert!(self.id.is_type());

        let mut checked_params = Vec::with_capacity(params.len());

        for Loc { item: param, .. } in params {
            match self.scopes.last().unwrap().get(*param) {
                // duplicate parameters cannot occur!
                Some(conflict) => {
                    let error = LocalResError::DuplicateGenericTypeParams {
                        module: self.module,
                        ty: self.id.as_type().unwrap(),
                        first: conflict.ident,
                        second: param,
                    };

                    let package = self.env.get_module(self.module).package;
                    self.errors.push(ResError::LocalRes { package, error });
                }
                // no overlapping parameter name
                None => {
                    let id = self.fresh();

                    self.insert(Binding {
                        ident: param,
                        id: ast::BindingId::Local(id),
                    });

                    checked_params.push(ast::Name { content: param, id });
                }
            }
        }

        checked_params.into_boxed_slice()
    }

    // TERM VISITORS

    fn visit_term(
        &mut self,
        Spanned { item, span }: Spanned<ubd::Term>,
    ) -> Spanned<ast::Term<BoundResult>> {
        match item {
            ubd::Term::Fn(func) => {
                self.visit_fn(span.with(func)).map(ast::Term::Fn)
            }
            ubd::Term::ExternFn(extern_fn) => self
                .visit_extern_fn(span.with(extern_fn))
                .map(ast::Term::ExternFn),
            ubd::Term::Const(constant) => {
                self.visit_const(span.with(constant)).map(ast::Term::Const)
            }
        }
    }

    fn visit_fn(
        &mut self,
        Spanned {
            item:
                ubd::Fn {
                    name,
                    params,
                    return_ty,
                    body,
                },
            span,
        }: Spanned<ubd::Fn>,
    ) -> Spanned<ast::Fn<BoundResult>> {
        // DEBUG MODE SANITY CHECKS
        debug_assert!(self.id.is_term());

        // intern and annotate name
        let name = self.bind_global_with_ident(name, self.id);

        // enter parameter scope and visit parameters
        self.enter_new_scope(ScopeKind::FnDeclParams);
        let params = self.visit_parameters(params);

        // process return type, if any
        let return_ty = return_ty.map(|ty| self.visit_ty(ty));

        // process function body
        let body = self.visit_fn_body(body);

        span.with(ast::Fn {
            name,
            params,
            return_ty,
            body,
        })
    }

    fn visit_extern_fn(
        &mut self,
        Spanned {
            item:
                ubd::ExternFn {
                    name,
                    params,
                    return_ty,
                },
            span,
        }: Spanned<ubd::ExternFn>,
    ) -> Spanned<ast::ExternFn<BoundResult>> {
        // DEBUG MODE SANITY CHECKS
        debug_assert!(self.id.is_term());

        // intern and annotate name
        let name = self.bind_global_with_ident(name, self.id);

        // enter parameter scope and visit parameters
        self.enter_new_scope(ScopeKind::FnDeclParams);
        let params = self.visit_parameters(params);

        // process return type, if any
        let return_ty = return_ty.map(|ty| self.visit_ty(ty));

        span.with(ast::ExternFn {
            name,
            params,
            return_ty,
        })
    }

    fn visit_const(
        &mut self,
        Spanned {
            item: ubd::Const { name, ty, value },
            span,
        }: Spanned<ubd::Const>,
    ) -> Spanned<ast::Const<BoundResult>> {
        // DEBUG MODE SANITY CHECKS
        debug_assert!(self.id.is_term());

        // intern and annotate name
        let name = self.bind_global_with_ident(name, self.id);

        // process type annotation, if any
        let ty = ty.map(|ty| self.visit_ty(ty));

        // process rhs
        let value = self.visit_expr(value);

        span.with(ast::Const { name, ty, value })
    }

    fn visit_parameters(
        &mut self,
        Spanned { item, .. }: Spanned<SpanSeq<ubd::ast::Parameter>>,
    ) -> SpanSeq<ast::Parameter<BoundResult>> {
        // DEBUG MODE SANITY CHECKS
        debug_assert!(self.scope_kind().is_some_and(|scope| matches!(
            scope,
            ScopeKind::FnDeclParams | ScopeKind::LambdaParams
        )));

        let mut parameters = Vec::with_capacity(item.len());

        for param in item {
            parameters.push(self.visit_parameter(param));
        }

        parameters.into_boxed_slice()
    }

    fn visit_parameter(
        &mut self,
        Spanned {
            item: ubd::ast::Parameter { pattern, ty },
            span,
        }: Spanned<ubd::ast::Parameter>,
    ) -> Spanned<ast::Parameter<BoundResult>> {
        let pattern = self.visit_pattern(pattern);

        let ty = ty.map(|ty| self.visit_ty(ty));

        span.with(ast::Parameter { pattern, ty })
    }

    fn visit_fn_body(
        &mut self,
        Spanned { item, span }: Spanned<ubd::ast::FnBody>,
    ) -> SpanBox<ast::Expr<BoundResult>> {
        Box::new(match item {
            ubd::ast::FnBody::EqExpr(expr) => self.visit_expr(span.with(expr)),
            ubd::ast::FnBody::Block(block) => {
                self.visit_block(span.with(block)).map(ast::Expr::Block)
            }
        })
    }

    // EXPRESSION VISITORS

    fn visit_expr(
        &mut self,
        Spanned { item, span }: Spanned<ubd::ast::Expr>,
    ) -> Spanned<ast::Expr<BoundResult>> {
        match item {
            ubd::ast::Expr::Name(name) => {
                // try to project the unqualified path root into a local binding
                let local_root = name
                    .as_unqualified_path_ref()
                    .and_then(|elems| elems.first())
                    .and_then(|&ident| self.resolve_ident(ident).ok())
                    .and_then(|bound| bound.as_local());

                match local_root {
                    Some(_) => self.visit_compound_field_expr(
                        span.with(name.as_unqualified_path().unwrap()),
                    ),
                    None => {
                        let name = self.resolve_name(span.with(name));
                        span.with(ast::Expr::Name(name))
                    }
                }
            }
            ubd::ast::Expr::Literal(literal) => span.with(ast::Expr::Literal(
                self.visit_literal_expr(span.with(literal)).unwrap(),
            )),
            ubd::ast::Expr::List(list) => {
                let mut elems = Vec::with_capacity(list.len());

                for elem in list {
                    let expr = self.visit_expr(elem);
                    elems.push(expr);
                }

                span.with(ast::Expr::List(elems.into_boxed_slice()))
            }
            ubd::ast::Expr::Tuple(tuple) => {
                // simple sanity check
                debug_assert!(tuple.len() >= 2);

                let mut elems = Vec::with_capacity(tuple.len());

                for elem in tuple {
                    let expr = self.visit_expr(elem);
                    elems.push(expr);
                }

                span.with(ast::Expr::Tuple(elems.into_boxed_slice()))
            }
            ubd::ast::Expr::Paren(inner) => self.visit_expr(*inner),
            ubd::ast::Expr::Block(block) => {
                self.visit_block(span.with(*block)).map(ast::Expr::Block)
            }
            ubd::ast::Expr::Prefix { operator, operand } => {
                let (op, symbol) = self.prefix_op_id(*operator);
                let operand = self.visit_expr(*operand);

                span.with(op.with_operands(
                    operator.span.with(symbol),
                    Box::new([operand]),
                ))
            }
            ubd::ast::Expr::Binary { lhs, operator, rhs } => {
                let (op, symbol) = self.binary_op_id(*operator);
                let lhs = self.visit_expr(*lhs);
                let rhs = self.visit_expr(*rhs);

                span.with(op.with_operands(
                    operator.span.with(symbol),
                    Box::new([lhs, rhs]),
                ))
            }
            ubd::ast::Expr::Call {
                callee,
                args: old_args,
            } => {
                let mut args = Vec::with_capacity(old_args.len());

                for arg in old_args {
                    let arg = self.visit_expr(arg);
                    args.push(arg);
                }

                let callee = Box::new(self.visit_expr(*callee));
                let args = args.into_boxed_slice();

                span.with(ast::Expr::Call {
                    callee,
                    args,
                    kind: ast::CallExprKind::Normal,
                })
            }
            ubd::ast::Expr::Record { name, fields, base } => {
                let name = self.resolve_name(name);

                let constr = name
                    .clone()
                    .ok()
                    .map(|bound| bound.id())
                    .and_then(ast::BindingId::as_global)
                    .and_then(|res| match res {
                        Res::StructType(ty) => Some((
                            ty,
                            self.env.get_type(ty).ast.name().content.item,
                        )),
                        Res::TyConstr { ty, name } => Some((ty, name)),
                        _ => None,
                    });

                let fields = constr
                    .map(|(ty, constr)| {
                        let name = name.clone().unwrap();
                        self.visit_record_expr_fields(&name, ty, constr, fields)
                    })
                    .unwrap_or_default();

                let base = base.map(|base| Box::new(self.visit_expr(*base)));

                span.with(ast::Expr::RecordConstr { name, fields, base })
            }
            ubd::ast::Expr::Field { item, field } => match field.item {
                ubd::ast::FieldExprField::Ident(ident) => {
                    let item = Box::new(self.visit_expr(*item));
                    let field = self.intern_ident_in_module(
                        field.span.with(ident),
                        self.module,
                    );

                    span.with(ast::Expr::RecordField { item, field })
                }
                ubd::ast::FieldExprField::TupleIndex => {
                    let item = Box::new(self.visit_expr(*item));

                    let field: Spanned<Option<u32>> = {
                        let source = field
                            .span()
                            .with(self.get_spanned_str(field.span()));

                        // using the dec_int parser is fine, since all tuple
                        // indices are already valid decimal int literals
                        let index = literal::parse_dec_int_literal(source)
                            .map(|lit| *lit.value())
                            .ok()
                            .and_then(|x| u32::try_from(x).ok());

                        if index.is_none() {
                            self.emit_local_error(
                                LocalResError::TupleFieldOverflowError {
                                    module: self.module,
                                    span: field.span,
                                },
                            );
                        }

                        field.span.with(index)
                    };

                    span.with(ast::Expr::TupleField { item, field })
                }
            },
            ubd::ast::Expr::Lambda {
                params:
                    Spanned {
                        item: old_params,
                        span: params_span,
                    },
                body,
            } => {
                self.enter_new_scope(ScopeKind::LambdaParams);

                let params = match old_params {
                    ubd::ast::LambdaParams::Ident(ident) => {
                        // TODO: check for shadowing
                        let ident = self.bind_ident(params_span.with(ident));

                        let param = params_span.with(ast::Parameter {
                            pattern: params_span
                                .with(ast::Pattern::Name(Ok(ident))),
                            ty: None,
                        });

                        Box::new([param])
                    }
                    ubd::ast::LambdaParams::Parameters(params) => {
                        self.visit_parameters(params_span.with(params))
                    }
                };

                let body = Box::new(self.visit_expr(*body));
                self.leave_scope();

                span.with(ast::Expr::Lambda { params, body })
            }
            ubd::ast::Expr::Match {
                scrutinee,
                arms: old_arms,
            } => {
                let scrutinee = Box::new(self.visit_expr(*scrutinee));
                let mut arms = Vec::with_capacity(old_arms.len());

                for arm in old_arms.item {
                    let arm = self.visit_match_arm(arm);
                    arms.push(arm);
                }

                let arms = arms.into_boxed_slice();
                span.with(ast::Expr::Match { scrutinee, arms })
            }
            ubd::ast::Expr::IfElse {
                condition,
                consequence,
                alternative,
            } => {
                let condition = Box::new(self.visit_expr(*condition));
                let consequence = Box::new(self.visit_block(*consequence));
                let alternative =
                    alternative.map(|alt| Box::new(self.visit_block(*alt)));

                span.with(ast::Expr::IfElse {
                    condition,
                    consequence,
                    alternative,
                })
            }
        }
    }

    /// Visits a sequence of identifiers whose first element is locally bound
    /// and should be processed as a composite field expression rather than a
    /// path.
    fn visit_compound_field_expr(
        &mut self,
        Spanned { item, .. }: Spanned<SpanSeq<ubd::ast::Ident>>,
    ) -> Spanned<ast::Expr<BoundResult>> {
        // break off the first element to be processed as a local binding
        let (&root_ident, tail) = item
            .split_first()
            .expect("field expressions have at least one element");

        // resolve the root and lift it into an expression
        let root = root_ident
            .span
            .with(ast::Expr::Name(self.resolve_ident(root_ident)));

        // fold the tail into a chain of RecordField expressions
        tail.iter()
            .map(|&ident| self.intern_ident_in_module(ident, self.module))
            .fold(root, |expr, field| {
                let span = Span::join(expr.span, field.span);
                span.with(ast::Expr::RecordField {
                    item: Box::new(expr),
                    field,
                })
            })
    }

    fn visit_literal_expr(
        &mut self,
        Spanned {
            item: literal,
            span,
        }: Spanned<ubd::ast::LiteralExpr>,
    ) -> Spanned<ast::LiteralExpr> {
        span.with(match literal {
            ubd::ast::LiteralExpr::Unit => ast::LiteralExpr::Unit,
            ubd::ast::LiteralExpr::Bool(value) => ast::LiteralExpr::Bool(value),
            ubd::ast::LiteralExpr::Char => {
                let source = span.with(self.get_spanned_str(span));

                match literal::parse_char_literal(source) {
                    Ok(lit) => ast::LiteralExpr::Char(*lit.value()),
                    Err(error) => {
                        self.emit_local_error(
                            LocalResError::CharLiteralError {
                                module: self.module,
                                error,
                            },
                        );

                        ast::LiteralExpr::Malformed(ast::MalformedLiteral::Char)
                    }
                }
            }
            ubd::ast::LiteralExpr::String => {
                let source = span.with(self.get_spanned_str(span));

                match literal::parse_string_literal(source) {
                    Ok(lit) => ast::LiteralExpr::String(
                        self.env.interner.intern(lit.value()),
                    ),
                    Err(error) => {
                        self.emit_local_error(
                            LocalResError::StringLiteralError {
                                module: self.module,
                                error,
                            },
                        );

                        ast::LiteralExpr::Malformed(
                            ast::MalformedLiteral::String,
                        )
                    }
                }
            }
            ubd::ast::LiteralExpr::BinInt => {
                let source = span.with(self.get_spanned_str(span));

                match literal::parse_bin_int_literal(source) {
                    Ok(lit) => ast::LiteralExpr::Int(*lit.value()),
                    Err(error) => {
                        self.emit_local_error(
                            LocalResError::IntLiteralOverflowError {
                                module: self.module,
                                error,
                            },
                        );

                        ast::LiteralExpr::Malformed(ast::MalformedLiteral::Int)
                    }
                }
            }
            ubd::ast::LiteralExpr::OctInt => {
                let source = span.with(self.get_spanned_str(span));

                match literal::parse_oct_int_literal(source) {
                    Ok(lit) => ast::LiteralExpr::Int(*lit.value()),
                    Err(error) => {
                        self.emit_local_error(
                            LocalResError::IntLiteralOverflowError {
                                module: self.module,
                                error,
                            },
                        );

                        ast::LiteralExpr::Malformed(ast::MalformedLiteral::Int)
                    }
                }
            }
            ubd::ast::LiteralExpr::DecInt => {
                let source = span.with(self.get_spanned_str(span));

                match literal::parse_dec_int_literal(source) {
                    Ok(lit) => ast::LiteralExpr::Int(*lit.value()),
                    Err(error) => {
                        self.emit_local_error(
                            LocalResError::IntLiteralOverflowError {
                                module: self.module,
                                error,
                            },
                        );

                        ast::LiteralExpr::Malformed(ast::MalformedLiteral::Int)
                    }
                }
            }
            ubd::ast::LiteralExpr::HexInt => {
                let source = span.with(self.get_spanned_str(span));

                match literal::parse_hex_int_literal(source) {
                    Ok(lit) => ast::LiteralExpr::Int(*lit.value()),
                    Err(error) => {
                        self.emit_local_error(
                            LocalResError::IntLiteralOverflowError {
                                module: self.module,
                                error,
                            },
                        );

                        ast::LiteralExpr::Malformed(ast::MalformedLiteral::Int)
                    }
                }
            }
            ubd::ast::LiteralExpr::Float => {
                let source = span.with(self.get_spanned_str(span));
                let float = literal::parse_float_literal(source);

                ast::LiteralExpr::Float(*float.value())
            }
        })
    }

    fn visit_record_expr_fields(
        &mut self,
        record_expr_name: &ast::Bound,
        ty: TypeId,
        constr: Symbol,
        old_fields: SpanSeq<ubd::ast::RecordExprField>,
    ) -> SpanSeq<ast::RecordExprField<BoundResult>> {
        let constr_fields = self
            .env
            .get_type(ty)
            .ast
            .as_adt()
            .map(|adt| &adt.constructors)
            .and_then(|constrs| constrs.get(&constr))
            .map(Spanned::item)
            .and_then(|constr| constr.payload())
            .map(Spanned::item)
            .and_then(ast::TyConstrPayload::as_record)
            .cloned(); // HACK: this clone can probably be avoided

        if let Some(constr_fields) = constr_fields {
            let mut fields = Vec::with_capacity(old_fields.len());

            for Spanned {
                item: ubd::ast::RecordExprField { field, value },
                span,
            } in old_fields
            {
                let field = self.intern_ident_in_module(field, self.module);

                let value = value
                    .map(|expr| self.visit_expr(expr))
                    .unwrap_or_else(|| {
                        let local =
                            self.resolve_symbol(field).ok_or_else(|| {
                                field
                                    .span
                                    .with(ast::NameContent::from(field.item))
                            });
                        self.name_from_bound_result(local)
                    });

                // if the field does not exist, emit an error and do
                // not insert the field into the expression
                if !constr_fields.contains_key(&field) {
                    self.emit_local_error(
                        LocalResError::NoSuchRecordExprField {
                            module: self.module,
                            constr: (ty, constr),
                            field,
                        },
                    );

                    continue;
                }

                fields.push(span.with(ast::RecordExprField { field, value }));
            }

            fields.into_boxed_slice()
        } else {
            self.emit_local_error(LocalResError::NotARecordConstr {
                module: self.module,
                name: record_expr_name.clone().content(),
            });
            Default::default()
        }
    }

    fn visit_match_arm(
        &mut self,
        Spanned {
            item: ubd::ast::MatchArm { pattern, body },
            span,
        }: Spanned<ubd::ast::MatchArm>,
    ) -> Spanned<ast::MatchArm<BoundResult>> {
        self.enter_new_scope(ScopeKind::MatchArm);
        let pattern = self.visit_pattern(pattern);
        let body = self.visit_expr(body);
        self.leave_scope();

        span.with(ast::MatchArm { pattern, body })
    }

    fn visit_block(
        &mut self,
        Spanned {
            item:
                ubd::ast::Block {
                    statements: old_statements,
                    return_expr,
                },
            span,
        }: Spanned<ubd::ast::Block>,
    ) -> Spanned<ast::Block<BoundResult>> {
        self.enter_new_scope(ScopeKind::Block);
        let mut statements = Vec::with_capacity(old_statements.len());

        for stmt in old_statements {
            let stmt = self.visit_stmt(stmt);
            statements.push(stmt);
        }

        let statements = statements.into_boxed_slice();
        let return_expr = return_expr.map(|ret| Box::new(self.visit_expr(ret)));

        // there could be arbitrarily many `LetStmt` scopes within the block,
        // so we use this method to remove them all at once by just truncating
        // the scope stack
        self.leave_block_scope();

        span.with(ast::Block {
            statements,
            return_expr,
        })
    }

    fn visit_stmt(
        &mut self,
        Spanned { item: stmt, span }: Spanned<ubd::ast::Stmt>,
    ) -> Spanned<ast::Stmt<BoundResult>> {
        span.with(match stmt {
            ubd::ast::Stmt::Empty => ast::Stmt::Empty,
            ubd::ast::Stmt::Expr(expr) => {
                let expr = self.visit_expr(expr).item;
                ast::Stmt::Expr(expr)
            }
            ubd::ast::Stmt::Let { pattern, ty, value } => {
                // reverse order: the pattern should not be visible within
                // the value expression, so we resolve value and ty within
                // the current scope before pushing a new scope onto the
                // stack and resolving the binding pattern itself

                let value = self.visit_expr(value);
                let ty = ty.map(|ty| self.visit_ty(ty));

                self.enter_new_scope(ScopeKind::LetStmt);
                let pattern = self.visit_pattern(pattern);

                ast::Stmt::Let { pattern, ty, value }
            }
        })
    }

    fn prefix_op_id(
        &mut self,
        operator: ubd::ast::PrefixOp,
    ) -> (Operator, Symbol) {
        match operator {
            ubd::ast::PrefixOp::Bang => {
                core_operator!(self, "bool", "not", "!")
            }
            ubd::ast::PrefixOp::Star => {
                core_operator!(self, "ref", "deref", "*")
            }
            ubd::ast::PrefixOp::Minus => {
                core_operator!(self, "int", "neg", "-")
            }
            ubd::ast::PrefixOp::MinusDot => {
                core_operator!(self, "float", "neg", "-.")
            }
        }
    }

    fn binary_op_id(
        &mut self,
        operator: ubd::ast::BinaryOp,
    ) -> (Operator, Symbol) {
        match operator {
            ubd::ast::BinaryOp::Carat => {
                core_operator!(self, "int", "pow", "^")
            }
            ubd::ast::BinaryOp::CaratDot => {
                core_operator!(self, "float", "pow", "^.")
            }
            ubd::ast::BinaryOp::LeftPipe => {
                core_operator!(self, "fun", "pipe_left", "<|")
            }
            ubd::ast::BinaryOp::RightPipe => {
                core_operator!(self, "fun", "pipe_right", "|>")
            }
            ubd::ast::BinaryOp::EqEq => {
                core_operator!(self, "cmp", "eq", "==")
            }
            ubd::ast::BinaryOp::BangEq => {
                core_operator!(self, "cmp", "neq", "!=")
            }
            ubd::ast::BinaryOp::Gt => {
                core_operator!(self, "int", "gt", ">")
            }
            ubd::ast::BinaryOp::GtDot => {
                core_operator!(self, "float", "gt", ">.")
            }
            ubd::ast::BinaryOp::Lt => {
                core_operator!(self, "int", "lt", "<")
            }
            ubd::ast::BinaryOp::LtDot => {
                core_operator!(self, "float", "lt", "<.")
            }
            ubd::ast::BinaryOp::Geq => {
                core_operator!(self, "int", "geq", ">=")
            }
            ubd::ast::BinaryOp::GeqDot => {
                core_operator!(self, "float", "geq", ">=.")
            }
            ubd::ast::BinaryOp::Leq => {
                core_operator!(self, "int", "leq", "<=")
            }
            ubd::ast::BinaryOp::LeqDot => {
                core_operator!(self, "float", "leq", "<=.")
            }
            ubd::ast::BinaryOp::Plus => {
                core_operator!(self, "int", "add", "+")
            }
            ubd::ast::BinaryOp::PlusDot => {
                core_operator!(self, "float", "add", "+.")
            }
            ubd::ast::BinaryOp::Minus => {
                core_operator!(self, "int", "sub", "-")
            }
            ubd::ast::BinaryOp::MinusDot => {
                core_operator!(self, "float", "sub", "-.")
            }
            ubd::ast::BinaryOp::Star => {
                core_operator!(self, "int", "mul", "*")
            }
            ubd::ast::BinaryOp::StarDot => {
                core_operator!(self, "float", "mul", "*.")
            }
            ubd::ast::BinaryOp::Slash => {
                core_operator!(self, "int", "div", "/")
            }
            ubd::ast::BinaryOp::SlashDot => {
                core_operator!(self, "float", "div", "/.")
            }
            ubd::ast::BinaryOp::Percent => {
                core_operator!(self, "int", "mod", "%")
            }
            ubd::ast::BinaryOp::Cons => {
                core_operator!(self, "list", "cons", "::")
            }
            ubd::ast::BinaryOp::PlusPlus => {
                core_operator!(self, "list", "append", "++")
            }
            ubd::ast::BinaryOp::Walrus => {
                core_operator!(self, "ref", "update", ":=")
            }
            // primitive operators without corresponding definitions
            // in the core library
            ubd::ast::BinaryOp::AmpAmp => {
                let sym = self.env.interner.intern_static("&&");
                (Operator::LazyAnd, sym)
            }
            ubd::ast::BinaryOp::BarBar => {
                let sym = self.env.interner.intern_static("||");
                (Operator::LazyOr, sym)
            }
            ubd::ast::BinaryOp::LeftArrow => {
                let sym = self.env.interner.intern_static("<-");
                (Operator::Mutate, sym)
            }
        }
    }

    // PATTERN VISITORS

    fn visit_pattern(
        &mut self,
        Spanned {
            item: pattern,
            span,
        }: Spanned<ubd::ast::Pattern>,
    ) -> Spanned<ast::Pattern<BoundResult>> {
        span.with(match pattern {
            ubd::ast::Pattern::Wildcard => ast::Pattern::Wildcard,
            ubd::ast::Pattern::Name(name) => {
                let res = match name {
                    ubd::ast::Name::Path(qualifier, elems) => {
                        let path = self.intern_path(span, qualifier, &elems);
                        self.resolve_interned_path(path.clone()).map_err(
                            |error| {
                                self.emit_local_error(error);
                                let Spanned { item, span } = path;
                                span.with(ast::NameContent::from(item))
                            },
                        )
                    }
                    // an identifier in a pattern is always a new local binding
                    ubd::ast::Name::Ident(ident) => {
                        // TODO: check for shadowing
                        Ok(self.bind_ident(span.with(ident)))
                    }
                };

                ast::Pattern::Name(res)
            }
            ubd::ast::Pattern::Literal(literal) => ast::Pattern::Literal(
                self.visit_literal_expr(span.with(literal)).unwrap(),
            ),
            ubd::ast::Pattern::Tuple(tuple) => {
                let mut elems = Vec::with_capacity(tuple.len());

                for elem in tuple {
                    let elem = self.visit_pattern(elem);
                    elems.push(elem);
                }

                ast::Pattern::Tuple(elems.into_boxed_slice())
            }
            ubd::ast::Pattern::List(list) => {
                let mut elems = Vec::with_capacity(list.len());

                for elem in list {
                    let elem = self.visit_pattern(elem);
                    elems.push(elem);
                }

                ast::Pattern::List(elems.into_boxed_slice())
            }
            ubd::ast::Pattern::Paren(inner) => {
                // NOTE: we're dropping the span of `inner` in favour of the
                // span of the entire parenthesized pattern; this is *probably*
                // fine but might be annoying later down the line

                self.visit_pattern(*inner).unwrap()
            }
            ubd::ast::Pattern::Cons { head, tail } => {
                let head = Box::new(self.visit_pattern(*head));
                let tail = Box::new(self.visit_pattern(*tail));

                ast::Pattern::Cons { head, tail }
            }
            ubd::ast::Pattern::TupleConstr { name, elems } => {
                let name = self.resolve_name(name);

                let elems = {
                    let mut res_elems = Vec::with_capacity(elems.len());

                    for elem in elems {
                        let elem = self.visit_pattern(elem);
                        res_elems.push(elem);
                    }

                    res_elems.into_boxed_slice()
                };

                ast::Pattern::TupleConstr { name, elems }
            }
            ubd::ast::Pattern::Record { name, fields, rest } => {
                let name = self.resolve_name(name);

                let fields = {
                    let mut res_fields = Vec::with_capacity(fields.len());

                    for field in fields {
                        let field = self.visit_record_pattern_field(field);
                        res_fields.push(field);
                    }

                    res_fields.into_boxed_slice()
                };

                ast::Pattern::RecordConstr { name, fields, rest }
            }
        })
    }

    fn visit_record_pattern_field(
        &mut self,
        Spanned {
            item: ubd::ast::RecordPatternField { field, pattern },
            span,
        }: Spanned<ubd::ast::RecordPatternField>,
    ) -> Spanned<ast::RecordPatternField<BoundResult>> {
        let field = self.intern_ident_in_module(field, self.module);

        let pattern = pattern
            .map(|pat| self.visit_pattern(pat))
            .unwrap_or_else(|| {
                // if there is no pattern, we synthesize a name pattern
                // with the same name as the field, so e.g. `Foo { bar }`
                // is desugared to `Foo { bar: bar }`.

                let name = self.bind_local_symbol(field);
                field.span.with(ast::Pattern::Name(Ok(name)))
            });

        span.with(ast::RecordPatternField { field, pattern })
    }

    // TYPE EXPRESSION VISITORS

    fn visit_ty(
        &mut self,
        Spanned { item, span }: Spanned<ubd::ast::Ty>,
    ) -> Spanned<ast::Ty<BoundResult>> {
        self.enter_new_scope(ScopeKind::Type);

        span.with(match item {
            ubd::ast::Ty::Infer => ast::Ty::Infer,
            ubd::ast::Ty::Prim(ubd::ast::PrimTy::Never) => ast::Ty::Never,
            ubd::ast::Ty::Prim(ubd::ast::PrimTy::Unit) => ast::Ty::Unit,
            ubd::ast::Ty::Prim(ubd::ast::PrimTy::Bool) => ast::Ty::Bool,
            ubd::ast::Ty::Prim(ubd::ast::PrimTy::Char) => ast::Ty::Char,
            ubd::ast::Ty::Prim(ubd::ast::PrimTy::String) => ast::Ty::String,
            ubd::ast::Ty::Prim(ubd::ast::PrimTy::Int) => ast::Ty::Int,
            ubd::ast::Ty::Prim(ubd::ast::PrimTy::Float) => ast::Ty::Float,
            ubd::ast::Ty::Paren(inner) => self.visit_ty(*inner).unwrap(),
            ubd::ast::Ty::Tuple(tuple) => {
                let mut tys = Vec::with_capacity(tuple.len());

                for ty in tuple {
                    tys.push(self.visit_ty(ty));
                }

                ast::Ty::Tuple(tys.into_boxed_slice())
            }
            ubd::ast::Ty::Fn { domain, codomain } => {
                let domain = {
                    let Spanned { item: domain, span } = *domain;
                    let mut tys = Vec::with_capacity(domain.len());

                    match domain {
                        ubd::ast::FnTyArgs::NoParens(ty) => {
                            tys.push(self.visit_ty(span.with(ty)))
                        }
                        ubd::ast::FnTyArgs::Parens(domain) => {
                            for ty in domain {
                                tys.push(self.visit_ty(ty));
                            }
                        }
                    };

                    span.with(tys.into_boxed_slice())
                };

                let codomain = Box::new(self.visit_ty(*codomain));

                ast::Ty::Fn { domain, codomain }
            }
            ubd::ast::Ty::Name(name) => {
                let name = self.resolve_or_bind_name(span.with(name));
                let args = Box::new([]); // empty list

                ast::Ty::Named { name, args }
            }
            ubd::ast::Ty::Generic { name, args } => {
                let name = self.resolve_or_bind_name(name);

                let args = {
                    let mut tys = Vec::with_capacity(args.len());

                    for arg in args {
                        tys.push(self.visit_ty(arg));
                    }

                    tys.into_boxed_slice()
                };

                ast::Ty::Named { name, args }
            }
        })
    }

    // NAME & IDENT VISITORS

    // there are two verbs in this section: `bind` and `resolve`. we use `bind`
    // to express that a method will insert a new binding in the current scope,
    // while `resolve` indicates that a function will try to match against the
    // current resolution environment. functions named `resolve_or_bind_*` will
    // first try to `resolve`, but if this fails then they will `bind` — this
    // is useful for contexts where names can be introduced implicitly, like in
    // generic type parameter lists.
    //
    // `resolve_or_bind_name` is a special case, since it will only produce a
    // new binding in the `Name::Ident` case. this is because paths cannot
    // implicitly introduce names into scope.

    fn resolve_name(
        &mut self,
        Spanned { item, span }: Spanned<ubd::ast::Name>,
    ) -> BoundResult {
        match item {
            ubd::ast::Name::Ident(ident) => {
                self.resolve_ident(span.with(ident))
            }
            ubd::ast::Name::Path(qualifier, ref elements) => {
                let path = self.intern_path(span, qualifier, elements);

                // HACK: this clone is probably unnecessary
                self.resolve_interned_path(path.clone()).map_err(|error| {
                    self.errors.push(ResError::LocalRes {
                        package: self.env.get_module(self.module).package,
                        error,
                    });

                    path.map(ast::NameContent::Path)
                })
            }
        }
    }

    fn resolve_or_bind_name(
        &mut self,
        Spanned { item: name, span }: Spanned<ubd::ast::Name>,
    ) -> BoundResult {
        match name {
            ubd::ast::Name::Ident(ident) => {
                Ok(self.resolve_or_bind_ident(span.with(ident)))
            }
            ubd::ast::Name::Path(qualifier, ref elements) => {
                let path = self.intern_path(span, qualifier, elements);

                // HACK: this clone is probably unnecessary
                self.resolve_interned_path(path.clone()).map_err(|error| {
                    self.errors.push(ResError::LocalRes {
                        package: self.env.get_module(self.module).package,
                        error,
                    });

                    path.map(ast::NameContent::Path)
                })
            }
        }
    }

    fn resolve_interned_path(
        &mut self,
        Spanned { item: path, span }: Spanned<ast::Path>,
    ) -> Result<ast::Bound, LocalResError> {
        // convert the qualifier (if any) into a module
        let qualified_module = match path.qualifier.map(Spanned::unwrap) {
            Some(Qualifier::Super) => {
                match self.env.get_module(self.module).parent {
                    Some(parent) => Some(parent),
                    // `super` in the root module of a package is nonsense
                    None => {
                        // we have to use return here explicitly, otherwise
                        // if we use postfix `?` the borrow checker gets mad
                        return Err(LocalResError::UsedSuperInRootModule {
                            module: self.module,
                            super_span: path.qualifier.unwrap().span,
                            path: span.with(path),
                        });
                    }
                }
            }
            Some(Qualifier::Package) => Some(
                self.env
                    .get_package(self.env.get_module(self.module).package)
                    .root_module,
            ),
            Some(Qualifier::Self_) => Some(self.module),
            None => None,
        };

        #[derive(Debug, Clone, Copy)]
        enum QS {
            Q(Qualifier),
            S(Symbol),
        }

        impl Spanned<QS> {
            fn as_symbol(self) -> Option<Spanned<Symbol>> {
                if let QS::S(symbol) = self.item {
                    Some(self.span.with(symbol))
                } else {
                    None
                }
            }
        }

        impl From<Spanned<Symbol>> for Spanned<QS> {
            fn from(value: Spanned<Symbol>) -> Self {
                value.span.with(QS::S(value.item))
            }
        }

        impl From<Spanned<Qualifier>> for Spanned<QS> {
            fn from(value: Spanned<Qualifier>) -> Self {
                value.span.with(QS::Q(value.item))
            }
        }

        let (start, remaining_elements) = match qualified_module {
            Some(module) => (
                ast::Name {
                    content: path.qualifier.unwrap().into(),
                    id: Res::Module(module),
                },
                path.elements.as_ref(),
            ),
            None => {
                let (head, tail) = path
                    .elements
                    .split_first()
                    .expect("An unqualified path cannot have zero elements");

                let id = match self.resolve_symbol(*head) {
                    // name resolved to a Res!
                    Some(ast::Bound::Path(ast::Name { id, .. }))
                    | Some(ast::Bound::Global(ast::Name { id, .. })) => id,
                    // name exists, but it is a local binding
                    Some(ast::Bound::Local(local)) => {
                        return Err(LocalResError::Path {
                            module: self.module,
                            error: LocalPathResError::StartsWithLocalBinding(
                                ast::Name {
                                    content: *head,
                                    ..local
                                },
                            ),
                            path: span.with(path),
                        })
                    }
                    // no such name in scope
                    None => {
                        return Err(LocalResError::Path {
                            module: self.module,
                            error: LocalPathResError::ElementDne(*head),
                            path: span.with(path),
                        })
                    }
                };

                (
                    ast::Name {
                        content: (*head).into(),
                        id,
                    },
                    tail,
                )
            }
        };

        // recursive helper function
        fn resolve_rec(
            resolver: &Resolver<'_>,
            start: ast::Name<Res, QS>,
            remaining_elements: &[Spanned<Symbol>],
        ) -> Result<Res, LocalPathResError> {
            match (start.id, remaining_elements) {
                // no elements left — return the start Res!
                (res, []) => Ok(res),
                // resolving from a module
                (Res::Module(module), [head, tail @ ..]) => {
                    match resolver.env.get_module(module).items.get(head) {
                        // resolved to public item
                        Some(item) if item.is_visible() => resolve_rec(
                            resolver,
                            ast::Name {
                                content: head.span.with(QS::S(head.item)),
                                id: item.item.item,
                            },
                            tail,
                        ),
                        // resolved to private item
                        Some(item) => {
                            Err(LocalPathResError::Private(ast::Name {
                                content: *head,
                                id: item.item.item,
                            }))
                        }
                        // no such item
                        None => Err(LocalPathResError::ElementDne(*head)),
                    }
                }
                // resolving from a type to one of its constructors
                (Res::Type(ty) | Res::StructType(ty), [constr]) => {
                    let ast = &resolver.get_stale_type(ty).ast;

                    match ast.item() {
                        // type aliases do not have constructors
                        ubd::Type::Alias(_) => {
                            Err(LocalPathResError::TypeConstrOfTypeAlias {
                                ty: ast::Name {
                                    content: start.content.as_symbol().unwrap(),
                                    id: ty,
                                },
                                constr: *constr,
                            })
                        }
                        // extern types do not have constructors
                        ubd::Type::Extern(_) => {
                            Err(LocalPathResError::TypeConstrOfExternType {
                                ty: ast::Name {
                                    content: start.content.as_symbol().unwrap(),
                                    id: ty,
                                },
                                constr: *constr,
                            })
                        }
                        // constructors of opaque ADTs are private
                        ubd::Type::Adt(ubd::Adt {
                            opacity: Some(_), ..
                        }) => Err(LocalPathResError::TypeConstrOfOpaqueAdt {
                            ty: ast::Name {
                                content: start.content.as_symbol().unwrap(),
                                id: ty,
                            },
                            constr: *constr,
                        }),
                        // otherwise, we might have something!
                        ubd::Type::Adt(adt) => {
                            match adt.constructors.get(constr) {
                                // success! the constructor exists
                                Some(_) => Ok(Res::TyConstr {
                                    ty,
                                    name: constr.item,
                                }),
                                // no such type constructor
                                None => Err(LocalPathResError::TypeConstrDne {
                                    ty: ast::Name {
                                        content: start
                                            .content
                                            .as_symbol()
                                            .unwrap(),
                                        id: ty,
                                    },
                                    constr: *constr,
                                }),
                            }
                        }
                    }
                }
                // more than one element after a type!
                (Res::Type(ty) | Res::StructType(ty), tail @ [_, _, ..]) => {
                    Err(LocalPathResError::TooManyElementsAfterType {
                        ty: ast::Name {
                            content: start.content.as_symbol().unwrap(),
                            id: ty,
                        },
                        tail: tail.into(), // implicit clone
                    })
                }
                // nonterminal terms are automatically invalid
                (Res::Term(term), tail @ [_, ..]) => {
                    Err(LocalPathResError::NonTerminalTerm {
                        term: ast::Name {
                            content: start.content.as_symbol().unwrap(),
                            id: term,
                        },
                        tail: tail.into(), // implicit clone
                    })
                }
                // `start` will never be a type constructor, so this is fine
                (Res::TyConstr { .. }, _) => unreachable!(),
            }
        }

        match resolve_rec(self, start, remaining_elements) {
            Ok(id) => Ok(ast::Bound::Path(ast::Name {
                content: span.with(path),
                id,
            })),
            Err(error) => Err(LocalResError::Path {
                module: self.module,
                error,
                path: span.with(path),
            }),
        }
    }

    fn resolve_ident(
        &mut self,
        ident: Spanned<ubd::ast::Ident>,
    ) -> BoundResult {
        let symbol = self.intern_ident_in_module(ident, self.module);
        self.resolve_symbol(symbol).ok_or_else(|| {
            symbol.span.with(ast::NameContent::Ident(symbol.item))
        })
    }

    fn bind_ident(&mut self, ident: Spanned<ubd::ast::Ident>) -> ast::Bound {
        let symbol = self.intern_ident_in_module(ident, self.module);
        self.bind_local_symbol(symbol)
    }

    fn resolve_or_bind_ident(
        &mut self,
        ident: Spanned<ubd::ast::Ident>,
    ) -> ast::Bound {
        let symbol = self.intern_ident_in_module(ident, self.module);

        self.lookup(*symbol)
            .map(|name| name.id().with_ident(symbol))
            .unwrap_or_else(|| self.bind_local_symbol(symbol))
    }

    fn resolve_symbol(&self, symbol: Spanned<Symbol>) -> Option<ast::Bound> {
        self.lookup(*symbol)
            .map(|name| name.id().with_ident(symbol))
    }

    fn bind_local_symbol(&mut self, ident: Spanned<Symbol>) -> ast::Bound {
        let local = self.fresh_local(ident);
        // TODO: generate warnings for shadowing!
        self.insert(local);
        local.into()
    }

    fn name_from_bound_result(
        &mut self,
        bound: BoundResult,
    ) -> Spanned<ast::Expr<BoundResult>> {
        let span = bound_result_span(&bound);
        span.with(ast::Expr::Name(bound))
    }
}

/// The main entrypoint for module-local name resolution.
pub fn resolve(
    Env {
        files,
        packages,
        modules,
        terms,
        types,
        interner,
    }: ImportResEnv,
    warnings: &mut Vec<ResWarning>,
    errors: &mut Vec<ResError>,
) -> ResEnv {
    // we start by dumping most of the old environment into a new one, and
    // allocating new buffers with the right capacity for terms and types
    let mut env = Env {
        files,
        packages,
        modules,
        interner,
        terms: Vec::with_capacity(terms.len()),
        types: Vec::with_capacity(types.len()),
    };

    // HACK: we're going to have to clone the types and keep around a buffer
    // of stale types in the Resolver so we can do path resolution
    let stale_types = types.clone();

    // now we go over each term and type and linearly resolve the name they
    // use. we already have all the module scoped names available, so we
    // don't have to consider use-before-declaration problems: if a name
    // cannot be resolved, it is immediately an error

    // NOTE: it is *crucial* that we preserve the validity of TermId and
    // TypeId values into the given ImportResEnv, so we absolutely *cannot*
    // delete any terms or types. instead, we will mark them as malformed
    // and preserve as much information about them as possible

    for (raw_id, Type { name, module, ast }) in types.into_iter().enumerate() {
        let id = match ast.is_struct() {
            true => Res::StructType(TypeId(raw_id)),
            false => Res::Type(TypeId(raw_id)),
        };

        let mut resolver =
            Resolver::new(&mut env, &stale_types, warnings, errors, module, id);

        let ty = Type {
            name,
            module,
            ast: resolver.visit_type(ast),
        };

        env.types.push(ty);
    }

    // the ordering here (i.e. types before terms) is loadbearing, since we
    // rely on being able to examine the properties of types when doing term
    // name resolution

    for (raw_id, Term { name, module, ast }) in terms.into_iter().enumerate() {
        let id = Res::Term(TermId(raw_id));
        let mut resolver =
            Resolver::new(&mut env, &stale_types, warnings, errors, module, id);

        let term = Term {
            name,
            module,
            ast: resolver.visit_term(ast),
        };

        env.terms.push(term);
    }

    // finally we just return the environment, since the caller owns the
    // `warnings` and `errors` buffers
    env
}

#[cfg(test)]
mod tests {
    use crate::{cst::Parser, env::unbound::UnboundEnv, package as pkg};
    use std::{path::PathBuf, str::FromStr};

    use super::*;

    #[test]
    fn build_resolved_env_from_core() {
        // load package CSTs
        let path = PathBuf::from_str("../../libs/core").unwrap();
        let package = pkg::Package::load_files(path).unwrap();
        let mut parser = Parser::new().unwrap();

        // lower CSTs to unbound_lowered::Ast
        let package = package
            .map_modules(|file| parser.parse(file))
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound::Ast::try_from)
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound_lowered::Ast::from);

        // build unbound env
        let mut env = UnboundEnv::new();
        let (_core_symbol, ingest_warnings, ingest_errors) =
            env.consume_package(package, Box::new([]));

        dbg!(ingest_warnings);
        dbg!(ingest_errors);

        // build import_res env
        let (env, errors) = ImportResEnv::from_unbound_env(env);
        dbg!(errors.len());

        let mut warnings = Vec::new();
        let mut errors = Vec::new();

        // build resolved env
        let mut env = super::resolve(env, &mut warnings, &mut errors);

        let ref_ = env.interner.intern_static("ref");
        let ref_mod_id = env.magic_core_submodule(ref_).unwrap();
        let ref_mod = env.get_module(ref_mod_id);

        for (sym, item) in ref_mod.items.clone() {
            let name = env.interner.resolve(sym).unwrap();
            let (_vis, _span, res) = item.spread();

            let res_value = env.get_res(res);

            eprintln!("{} ({:?})\n{:?}\n\n", name, res, res_value);
        }

        dbg![warnings];
        dbg![errors];
    }
}
