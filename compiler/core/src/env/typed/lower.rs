//! The lowering and desugaring portion of the typechecking implementation.
//!
//! # Lowering
//! The entrypoint for lowering is the [`lower`] function, which takes a
//! [`ResEnv`] and returns a [`TypedEnv`]. More precisely, the resulting
//! [`TypedEnv`] is incomplete: every expression, constant, and function has
//! been assigned a type, but the overall program is not necessarily well-typed
//! or even completely well-formed.
//!
//! Aside from this main task—assigning types to expressions—the lowering phase
//! is also responsible for further desugaring of the syntax tree. Most of this
//! can be seen in the definition of [`ast::Expr`], in which block expressions
//! are desugared as [`ast::Expr::LetIn`] sequences and if-else expressions are
//! converted into match statements of a boolean-typed scrutinee.
//!
//! When type annotations occur, they are reified into [`ast::Ty`] values by an
//! appropriate method of [`TyReifier`]. This information is used to infer the
//! types of function and constant declarations, as well as of let-bindings and
//! lambda parameters.
//!
//! Finally, errors are produced for terms with the `pub` visibility modifier
//! and whose reified type is not concrete (i.e. contains unquantified type
//! variables).
//!

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{
    ast::typed::{Bound, Name},
    env::{
        Env, ModId, Res, TypeId,
        resolve::{BoundResult, ResEnv},
    },
    symbol::Symbol,
    unique::Uid,
};

use crate::{
    ast::{
        bound,
        common::Vis,
        typed::{self as ast, Typed},
    },
    env::{Term, Type},
    span::{Span, SpanBox, SpanSeq, Spanned},
};

use super::TypedEnv;

#[derive(Debug, Clone)]
pub enum TyLowerError {
    /// A public term has a non-concrete type.
    NonConcretePubTermTy { name: Symbol, module: ModId },
    /// An alias has a non-concrete right-hand side.
    NonConcreteAliasRhs { name: Symbol, module: ModId },
    /// A type parameter in the definition of a type declaration is unbound.
    PhantomTypeParameter { name: Name<Uid>, module: ModId },
    /// A type parameter in the body of a type declaration is unbound.
    UnboundTypeParameter {
        ty: Name<Res>,
        param: Uid,
        module: ModId,
    },
    /// A type alias is recursive.
    RecursiveAliasDecl {
        alias: Name<Res>,
        rhs_occurrence: Bound,
        module: ModId,
    },
    UsedTyParamAsPolytype {
        param: Name<Uid>,
        span: Span,
        module: ModId,
    },
}

pub fn lower(
    Env {
        files,
        packages,
        modules,
        terms: untyped_terms,
        types: untyped_types,
        interner,
    }: ResEnv,
) -> (TypedEnv, Vec<TyLowerError>) {
    let mut errors = Vec::new();

    let types = {
        let mut types = Vec::with_capacity(untyped_types.len());

        for (raw_index, Type { name, module, ast }) in
            untyped_types.into_iter().enumerate()
        {
            let id = TypeId(raw_index);
            let ty_name = ast.name();
            let ty_params: HashSet<_> =
                ast.params().iter().map(|binding| binding.id).collect();
            let mut lowerer =
                TypeLowerer::new(module, id, ty_name, &ty_params, &mut errors);
            let ast = lowerer.lower_type(ast);
            types.push(Type { name, module, ast });
        }

        types
    };

    let terms = {
        let mut terms = Vec::with_capacity(untyped_terms.len());

        for Term { name, module, ast } in untyped_terms {
            let mut ty_params = HashSet::new();
            let mut lowerer =
                TermLowerer::new(module, &mut ty_params, &mut errors);
            let ast = lowerer.lower_term(ast);

            let is_public =
                // SAFETY: the `modules` vec and `module` id come from
                // the same well-formed environment
                unsafe { crate::env::blind_module_index(&modules, module) }
                    .items
                    .get(&name)
                    .map(Vis::is_visible)
                    .unwrap_or(false);

            if !ast.ty.is_concrete() && is_public {
                let error = TyLowerError::NonConcretePubTermTy { name, module };
                errors.push(error);
            }

            terms.push(Term { name, module, ast });
        }

        terms
    };

    (
        Env {
            files,
            packages,
            modules,
            terms,
            types,
            interner,
        },
        errors,
    )
}

struct TypeLowerer<'a> {
    module: ModId,
    id: TypeId,
    ty_name: Name<Res>,
    ty_params: &'a HashSet<Uid>,
    errors: &'a mut Vec<TyLowerError>,
}

impl<'a> TypeLowerer<'a> {
    pub fn new(
        module: ModId,
        id: TypeId,
        ty_name: Name<Res>,
        ty_params: &'a HashSet<Uid>,
        errors: &'a mut Vec<TyLowerError>,
    ) -> Self {
        Self {
            module,
            id,
            ty_name,
            ty_params,
            errors,
        }
    }

    /// Projects a mutable reference to `self` into a [`TyReifier`].
    pub fn reifier<'r>(&'r mut self) -> TyReifier<'r> {
        TyReifier::new(self.module, self.ty_params, self.errors)
    }

    pub fn lower_type(
        &mut self,
        Spanned { item, span }: Spanned<bound::Type<BoundResult>>,
    ) -> Spanned<ast::Type<BoundResult>> {
        let (attrs, name, params, kind) = match item {
            bound::Type::Alias(bound::TypeAlias {
                attrs,
                name,
                params,
                ty,
            }) => {
                let rhs_ty = {
                    let mut reifier = self.reifier();
                    let matrix = reifier.reify_ty_matrix(ty.as_ref());
                    reifier.quantify(matrix)
                };

                // alias rhs concreteness check
                if !rhs_ty.is_concrete() {
                    let error = TyLowerError::NonConcreteAliasRhs {
                        name: *name.content,
                        module: self.module,
                    };

                    self.errors.push(error);
                }

                // variable binding checks
                let bound_vars = rhs_ty.bound_vars();
                self.check_bound_type_variables(&params, bound_vars);

                // alias recursiveness check
                let alias_occurences = rhs_ty.names_with(|bound_result| {
                    bound_result.as_ref().is_ok_and(|res_name| {
                        res_name.as_res() == Some(name.id)
                    })
                });

                for occurrence in alias_occurences {
                    let occurrence = occurrence.unwrap();
                    let error = TyLowerError::RecursiveAliasDecl {
                        alias: name,
                        rhs_occurrence: occurrence,
                        module: self.module,
                    };

                    self.errors.push(error);
                }

                (
                    attrs,
                    name,
                    params,
                    ast::TypeKind::Alias {
                        rhs_ast: ty,
                        rhs_ty,
                    },
                )
            }
            bound::Type::Adt(bound::Adt {
                attrs,
                name,
                opacity,
                params,
                constructors,
            }) => {
                let constrs = self.lower_constructors(constructors, &params);

                // aggregate bound type variables over all constructors and
                // perform binding check
                let mut bound_vars = HashSet::new();

                for constr in constrs.values() {
                    let constr_kind = &constr.item().kind;

                    match constr_kind {
                        ast::TyConstrKind::Unit(_) => (),
                        ast::TyConstrKind::Record(fields) => {
                            for var in fields
                                .values()
                                .flat_map(|field| field.ty.bound_vars())
                            {
                                bound_vars.insert(var);
                            }
                        }
                        ast::TyConstrKind::Tuple { elems, fn_ty: _ } => {
                            for var in
                                elems.iter().flat_map(|ty| ty.bound_vars())
                            {
                                bound_vars.insert(var);
                            }
                        }
                    }
                }

                self.check_bound_type_variables(&params, bound_vars);

                (attrs, name, params, ast::TypeKind::Adt { opacity, constrs })
            }
            bound::Type::Extern(bound::ExternType {
                attrs,
                name,
                params,
            }) => (attrs, name, params, ast::TypeKind::Extern),
        };

        span.with(ast::Type {
            attrs,
            name,
            params,
            kind,
        })
    }

    /// Given a list of type parameters and a set of bound type variables, checks
    /// 1. that each parameter occurs among the bound variables;
    /// 2. that each bound variable has a corresponding parameter.
    ///
    /// If either case occurs then an error is produced in `self`.
    pub fn check_bound_type_variables(
        &mut self,
        params: &[Name<Uid>],
        mut bound_vars: HashSet<Uid>,
    ) {
        for param in params {
            if !bound_vars.contains(&param.id) {
                let error = TyLowerError::PhantomTypeParameter {
                    name: *param,
                    module: self.module,
                };

                self.errors.push(error);
            }

            let _ = bound_vars.remove(&param.id);
        }

        for var in bound_vars {
            let error = TyLowerError::UnboundTypeParameter {
                ty: self.ty_name,
                param: var,
                module: self.module,
            };

            self.errors.push(error);
        }
    }

    pub fn lower_constructors(
        &mut self,
        constrs: HashMap<Symbol, Spanned<bound::TyConstr<BoundResult>>>,
        params: &[Name<Uid>],
    ) -> HashMap<Symbol, Spanned<ast::TyConstr<BoundResult>>> {
        assert!(self.ty_name.id.is_type());

        let (prefix, args) = {
            let mut prefix = HashSet::with_capacity(params.len());
            let mut args = Vec::with_capacity(params.len());

            for Name { id, .. } in params {
                prefix.insert(*id);
                args.push(Arc::new(ast::TyMatrix::Var(*id)));
            }

            (prefix, args.into_boxed_slice())
        };

        let matrix = {
            let name = Ok(Bound::Global(self.ty_name));
            Arc::new(ast::TyMatrix::Named { name, args })
        };

        let ty = Arc::new(ast::Ty {
            prefix: prefix.clone(),
            matrix: matrix.clone(),
        });

        constrs
            .into_iter()
            .map(|(symbol, ast)| {
                let name = ast.name;

                let kind = match ast.payload.as_ref().map(Spanned::item) {
                    None => ast::TyConstrKind::Unit(ty.clone()),
                    Some(bound::TyConstrPayload::Tuple(tys)) => {
                        // we project a reifier, but we don't necessarily use
                        // the prefix that it collects; each constructor will
                        // use the prefix obtained by processing the type
                        let mut reifier = self.reifier();

                        // reify each component matrix
                        let elem_matrices: Box<[_]> = tys
                            .iter()
                            .map(|ty| reifier.reify_ty_matrix(ty.as_ref()))
                            .collect();

                        // build the function type matrix
                        let fn_ty_matrix = Arc::new(ast::TyMatrix::Fn {
                            domain: elem_matrices.clone(),
                            codomain: matrix.clone(),
                        });

                        // quantify the component matrices
                        let elems: Box<[_]> = elem_matrices
                            .into_iter()
                            .map(|matrix| ast::Ty {
                                prefix: prefix.clone(),
                                matrix,
                            })
                            .map(Arc::new)
                            .collect();

                        // quantify the function matrix
                        let fn_ty = Arc::new(ast::Ty {
                            prefix: prefix.clone(),
                            matrix: fn_ty_matrix,
                        });

                        ast::TyConstrKind::Tuple { elems, fn_ty }
                    }
                    Some(bound::TyConstrPayload::Record(fields)) => {
                        let mut reifier = self.reifier();

                        ast::TyConstrKind::Record(
                            fields
                                .iter()
                                .map(|(&symbol, field)| {
                                    let mutability = field.mutability;
                                    let name = field.name;
                                    let matrix = reifier
                                        .reify_ty_matrix(field.ty.as_ref());

                                    let ty = Arc::new(ast::Ty {
                                        prefix: prefix.clone(),
                                        matrix,
                                    });

                                    (
                                        symbol,
                                        ast::RecordField {
                                            mutability,
                                            name,
                                            ty,
                                        },
                                    )
                                })
                                .collect(),
                        )
                    }
                };

                let constr = ast.span.with(ast::TyConstr { name, kind, ast });
                (symbol, constr)
            })
            .collect()
    }
}

struct TermLowerer<'a> {
    module: ModId,
    ty_params: &'a mut HashSet<Uid>,
    errors: &'a mut Vec<TyLowerError>,
}

impl<'a> TermLowerer<'a> {
    pub fn new(
        module: ModId,
        ty_params: &'a mut HashSet<Uid>,
        errors: &'a mut Vec<TyLowerError>,
    ) -> Self {
        Self {
            module,
            ty_params,
            errors,
        }
    }

    /// Projects a mutable reference to `self` into a [`TyReifier`].
    pub fn reifier<'r>(&'r mut self) -> TyReifier<'r> {
        TyReifier::new(self.module, self.ty_params, self.errors)
    }

    pub fn lower_term(
        &mut self,
        Spanned { item, span }: Spanned<bound::Term<BoundResult>>,
    ) -> Spanned<ast::Term<BoundResult>> {
        let (attrs, name, ty, kind) = match item {
            bound::Term::Fn(bound::Fn {
                attrs,
                name,
                params,
                return_ty,
                body,
            }) => {
                let ty = {
                    let mut reifier = self.reifier();
                    let matrix = reifier.reify_fn_ty_annotation(
                        &params,
                        return_ty.as_ref().map(Spanned::as_ref),
                    );
                    reifier.quantify(matrix)
                };

                let kind = ast::TermKind::Fn {
                    params: self.lower_params(params),
                    body: self.lower_expr(*body),
                    return_ty,
                };

                (attrs, name, ty, kind)
            }
            bound::Term::ExternFn(bound::ExternFn {
                attrs,
                name,
                params,
                return_ty,
            }) => {
                let ty = {
                    let mut reifier = self.reifier();
                    let matrix = reifier.reify_fn_ty_annotation(
                        &params,
                        return_ty.as_ref().map(Spanned::as_ref),
                    );
                    reifier.quantify(matrix)
                };

                let kind = ast::TermKind::ExternFn {
                    params: self.lower_params(params),
                    return_ty,
                };

                (attrs, name, ty, kind)
            }
            bound::Term::Const(bound::Const {
                attrs,
                name,
                ty: ty_ast,
                value,
            }) => {
                let ty = {
                    let mut reifier = self.reifier();
                    let matrix = reifier.reify_option_ty_matrix(
                        ty_ast.as_ref().map(Spanned::as_ref),
                    );
                    reifier.quantify(matrix)
                };

                let kind = ast::TermKind::Const {
                    ty_ast,
                    value: self.lower_expr(value),
                };

                (attrs, name, ty, kind)
            }
        };

        span.with(ast::Term {
            attrs,
            name,
            ty,
            kind,
        })
    }

    pub fn lower_params(
        &mut self,
        params: SpanSeq<bound::Parameter<BoundResult>>,
    ) -> SpanSeq<ast::Parameter<BoundResult>> {
        params
            .into_iter()
            .map(|Spanned { item, span }| {
                span.with(ast::Parameter {
                    pattern: item.pattern,
                    ty_ast: item.ty,
                })
            })
            .collect()
    }

    pub fn lower_expr(
        &mut self,
        Spanned { item, span }: Spanned<bound::Expr<BoundResult>>,
    ) -> Spanned<Typed<ast::Expr<BoundResult>, BoundResult>> {
        span.with(match item {
            bound::Expr::Name(name) => {
                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::Name(name))
            }
            bound::Expr::Literal(literal_expr) => {
                let ty = Arc::new(ast::Ty::prim(match &literal_expr {
                    ast::LiteralExpr::Unit => ast::PrimTy::Unit,
                    ast::LiteralExpr::Bool(_) => ast::PrimTy::Bool,
                    ast::LiteralExpr::Char(_) => ast::PrimTy::Char,
                    ast::LiteralExpr::String(_) => ast::PrimTy::String,
                    ast::LiteralExpr::Int(_) => ast::PrimTy::Int,
                    ast::LiteralExpr::Float(_) => ast::PrimTy::Float,
                    ast::LiteralExpr::Malformed(lit) => match lit {
                        bound::MalformedLiteral::Char => ast::PrimTy::Char,
                        bound::MalformedLiteral::String => ast::PrimTy::String,
                        bound::MalformedLiteral::Int => ast::PrimTy::Int,
                    },
                }));

                ty.with(ast::Expr::Literal(literal_expr))
            }
            bound::Expr::List(elems) => {
                // NOTE: we could get a more precise type here by threading the
                // TypeId of core.list.List through as a parameter of lower_expr,
                // but it's less awkward to do this later during full typechecking

                let elems = elems
                    .into_iter()
                    .map(|elem| self.lower_expr(elem))
                    .collect();
                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::List(elems))
            }
            bound::Expr::Tuple(elems) => {
                let elems = elems
                    .into_iter()
                    .map(|elem| self.lower_expr(elem))
                    .collect::<Box<[_]>>();
                let ty = Arc::new(ast::Ty::fresh_unbound_tuple(elems.len()));
                ty.with(ast::Expr::Tuple(elems))
            }
            bound::Expr::Block(block) => self
                .lower_block_rec(block.statements.as_ref(), block.return_expr),
            bound::Expr::RecordConstr {
                name,
                fields: untyped_fields,
                base,
            } => {
                let fields = untyped_fields
                    .into_iter()
                    .map(
                        |Spanned {
                             span,
                             item: bound::RecordExprField { field, value },
                         }| {
                            let value = self.lower_expr(value);
                            let field = ast::RecordExprField { field, value };
                            span.with(field)
                        },
                    )
                    .collect();

                let base =
                    base.map(|base| self.lower_expr(*base)).map(Box::new);
                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::RecordConstr { name, fields, base })
            }
            bound::Expr::RecordField { item, field } => {
                let item = Box::new(self.lower_expr(*item));
                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::RecordField { item, field })
            }
            bound::Expr::TupleField { item, field } => {
                let item = Box::new(self.lower_expr(*item));
                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::TupleField { item, field })
            }
            bound::Expr::Lambda { params, body } => {
                let annotation = {
                    let mut reifier = self.reifier();
                    let matrix =
                        reifier.reify_fn_ty_annotation(params.as_ref(), None);
                    reifier.quantify(matrix)
                };

                let params = self.lower_params(params);
                let body = Box::new(self.lower_expr(*body));

                let ty = Arc::new(ast::Ty::fresh_unbound_fn(params.len()));
                ty.with(ast::Expr::Lambda {
                    annotation,
                    params,
                    body,
                })
            }
            bound::Expr::Call { callee, args, kind } => {
                let callee = Box::new(self.lower_expr(*callee));
                let args =
                    args.into_iter().map(|arg| self.lower_expr(arg)).collect();
                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::Call { callee, args, kind })
            }
            bound::Expr::LazyAnd { operator, lhs, rhs } => {
                let operator = operator.with(ast::BuiltinOperator::LazyAnd);
                let lhs = Box::new(self.lower_expr(*lhs));
                let rhs = Box::new(self.lower_expr(*rhs));

                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Bool));
                ty.with(ast::Expr::Builtin { operator, lhs, rhs })
            }
            bound::Expr::LazyOr { operator, lhs, rhs } => {
                let operator = operator.with(ast::BuiltinOperator::LazyOr);
                let lhs = Box::new(self.lower_expr(*lhs));
                let rhs = Box::new(self.lower_expr(*rhs));

                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Bool));
                ty.with(ast::Expr::Builtin { operator, lhs, rhs })
            }
            bound::Expr::Mutate { operator, lhs, rhs } => {
                let operator = operator.with(ast::BuiltinOperator::Mutate);
                let lhs = Box::new(self.lower_expr(*lhs));
                let rhs = Box::new(self.lower_expr(*rhs));

                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Unit));
                ty.with(ast::Expr::Builtin { operator, lhs, rhs })
            }
            bound::Expr::Match {
                scrutinee,
                arms: untyped_arms,
            } => {
                let scrutinee = Box::new(self.lower_expr(*scrutinee));

                let arms = untyped_arms
                    .into_iter()
                    .map(
                        |Spanned {
                             span,
                             item: bound::MatchArm { pattern, body },
                         }| {
                            let body = self.lower_expr(body);
                            let arm = ast::MatchArm { pattern, body };
                            span.with(arm)
                        },
                    )
                    .collect();

                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::Match { scrutinee, arms })
            }
            bound::Expr::IfElse {
                condition,
                consequence,
                alternative,
            } => {
                let consequence = consequence.span.with(ast::MatchArm {
                    pattern: consequence.span.with(ast::Pattern::Literal(
                        ast::LiteralExpr::Bool(true),
                    )),
                    body: consequence.span.with(self.lower_block_rec(
                        consequence.statements.as_ref(),
                        consequence.return_expr.clone(),
                    )),
                });

                let alternative_span = alternative
                    .as_deref()
                    .map(Spanned::span)
                    .unwrap_or(Span::ZERO);

                let alternative = alternative_span.with(ast::MatchArm {
                    pattern: alternative_span.with(ast::Pattern::Literal(
                        ast::LiteralExpr::Bool(false),
                    )),
                    body: alternative_span.with(
                        alternative
                            .map(|b| {
                                self.lower_block_rec(
                                    b.statements.as_ref(),
                                    b.return_expr.clone(),
                                )
                            })
                            .unwrap_or_else(generate_unit_expr),
                    ),
                });

                let scrutinee = Box::new(self.lower_expr(*condition));
                let arms = std::iter::once(consequence)
                    .chain(std::iter::once(alternative))
                    .collect::<Box<[_]>>();

                let ty = Arc::new(ast::Ty::fresh_unbound());
                ty.with(ast::Expr::Match { scrutinee, arms })
            }
        })
    }

    pub fn lower_block_rec(
        &mut self,
        stmts: &[Spanned<bound::Stmt<BoundResult>>],
        body: Option<SpanBox<bound::Expr<BoundResult>>>,
    ) -> Typed<ast::Expr<BoundResult>, BoundResult> {
        match stmts {
            [] => match body {
                Some(expr) => self.lower_expr(*expr).item,
                None => {
                    let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Unit));
                    ty.with(ast::Expr::Literal(ast::LiteralExpr::Unit))
                }
            },
            [Spanned { item, span }, tail @ ..] => match item {
                bound::Stmt::Empty => self.lower_block_rec(tail, body),
                bound::Stmt::Expr(expr) => {
                    let lhs = None;
                    let rhs =
                        Box::new(self.lower_expr(span.with(expr.clone())));
                    let body = Box::new(self.lower_block_rec(tail, body));

                    let ty = body.ty.clone();
                    ty.with(ast::Expr::LetIn { lhs, rhs, body })
                }
                bound::Stmt::Let { pattern, ty, value } => {
                    let lhs = Some(ast::LetStmtLhs {
                        pattern: pattern.clone(),
                        ty_ast: ty.clone(),
                    });
                    let rhs = Box::new(self.lower_expr(value.clone()));
                    let body = Box::new(self.lower_block_rec(tail, body));

                    let ty = body.ty.clone();
                    ty.with(ast::Expr::LetIn { lhs, rhs, body })
                }
            },
        }
    }
}

fn generate_unit_expr() -> Typed<ast::Expr<BoundResult>, BoundResult> {
    let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Unit));
    ty.with(ast::Expr::Literal(ast::LiteralExpr::Unit))
}

// TYPE AST REIFICATION

struct TyReifier<'a> {
    /// The current module.
    module: ModId,
    /// The type parameters in scope.
    ty_params: &'a HashSet<Uid>,
    /// The universally quantified prefix of the reified type.
    prefix: HashSet<Uid>,
    /// The errors that occurred while reifying.
    errors: &'a mut Vec<TyLowerError>,
}

impl<'a> TyReifier<'a> {
    /// Reifies a [`bound::Ty`] into an [`ast::TyMatrix`].
    pub fn reify_ty_matrix(
        &mut self,
        Spanned { span, item }: Spanned<&ast::TyAst<BoundResult>>,
    ) -> Arc<ast::TyMatrix<BoundResult>> {
        Arc::new(match item {
            bound::Ty::Infer => ast::TyMatrix::fresh_var(),
            bound::Ty::Never => ast::TyMatrix::Prim(ast::PrimTy::Never),
            bound::Ty::Unit => ast::TyMatrix::Prim(ast::PrimTy::Unit),
            bound::Ty::Bool => ast::TyMatrix::Prim(ast::PrimTy::Bool),
            bound::Ty::Char => ast::TyMatrix::Prim(ast::PrimTy::Char),
            bound::Ty::String => ast::TyMatrix::Prim(ast::PrimTy::String),
            bound::Ty::Int => ast::TyMatrix::Prim(ast::PrimTy::Int),
            bound::Ty::Float => ast::TyMatrix::Prim(ast::PrimTy::Float),
            bound::Ty::Tuple(elems) => ast::TyMatrix::Tuple(
                elems
                    .into_iter()
                    .map(|ty| self.reify_ty_matrix(ty.as_ref()))
                    .collect(),
            ),
            bound::Ty::Fn { domain, codomain } => ast::TyMatrix::Fn {
                domain: domain
                    .item
                    .iter()
                    .map(|ty| self.reify_ty_matrix(ty.as_ref()))
                    .collect(),
                codomain: self.reify_ty_matrix(codomain.as_ref().as_ref()),
            },
            bound::Ty::Named { name, args } => {
                // if name is locally bound, it must be a parameter
                if let Some(name @ Name { id, .. }) =
                    name.as_ref().ok().and_then(|b| b.as_local())
                {
                    // if the id is known to be a type parameter but it has been
                    // used with arguments, this is an error
                    if self.ty_params.contains(&id) && !args.is_empty() {
                        let error = TyLowerError::UsedTyParamAsPolytype {
                            param: name,
                            span,
                            module: self.module,
                        };

                        self.errors.push(error);
                    }

                    // add the id to the prefix and return
                    self.prefix.insert(id);
                    ast::TyMatrix::Var(id)
                } else {
                    // otherwise just process the name as expected
                    ast::TyMatrix::Named {
                        name: name.clone(),
                        args: args
                            .iter()
                            .map(|arg| self.reify_ty_matrix(arg.as_ref()))
                            .collect(),
                    }
                }
            }
        })
    }

    /// Reifies an _optional_ type annotation.
    ///
    /// Optional types differ from other types in that, when they are absent,
    /// the resulting inferred type should be an existential type variable.
    /// This is the same behaviour as the `_` inference placeholder.
    pub fn reify_option_ty_matrix(
        &mut self,
        ast: Option<Spanned<&ast::TyAst<BoundResult>>>,
    ) -> Arc<ast::TyMatrix<BoundResult>> {
        match ast {
            Some(ast) => self.reify_ty_matrix(ast),
            None => Arc::new(ast::TyMatrix::fresh_var()),
        }
    }

    /// Reifies the annotations of a function declaration into a type.
    pub fn reify_fn_ty_annotation(
        &mut self,
        parameters: &[Spanned<bound::Parameter<BoundResult>>],
        return_ty: Option<Spanned<&ast::TyAst<BoundResult>>>,
    ) -> Arc<ast::TyMatrix<BoundResult>> {
        Arc::new(ast::TyMatrix::Fn {
            domain: parameters
                .iter()
                .map(|Spanned { item, .. }| {
                    self.reify_option_ty_matrix(
                        item.ty.as_ref().map(Spanned::as_ref),
                    )
                })
                .collect(),
            codomain: self.reify_option_ty_matrix(return_ty),
        })
    }

    /// Consumes `self` to convert an [`ast::TyMatrix`] into an [`ast::Ty`].
    pub fn quantify(
        self,
        matrix: Arc<ast::TyMatrix<BoundResult>>,
    ) -> Arc<ast::Ty<BoundResult>> {
        let Self { prefix, .. } = self;
        Arc::new(ast::Ty { prefix, matrix })
    }

    /// Partially clones `self` to convert an [`ast::TyMatrix`] into an [`ast::Ty`].
    pub fn quantify_cloned(
        &self,
        matrix: Arc<ast::TyMatrix<BoundResult>>,
    ) -> Arc<ast::Ty<BoundResult>> {
        let prefix = self.prefix.clone();
        Arc::new(ast::Ty { prefix, matrix })
    }

    pub fn new(
        module: ModId,
        ty_params: &'a HashSet<Uid>,
        errors: &'a mut Vec<TyLowerError>,
    ) -> Self {
        Self {
            module,
            ty_params,
            errors,
            prefix: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        cst::Parser,
        env::{
            import_res::ImportResEnv, resolve::resolve, unbound::UnboundEnv,
        },
        package as pkg,
    };
    use std::{path::PathBuf, str::FromStr};

    #[test]
    fn build_lowered_env_from_core() {
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
        let env = resolve(env, &mut warnings, &mut errors);

        // lower to typed env
        let (mut env, lower_errors) = super::lower(env);

        // REF MODULE INSPECTION

        let ref_ = env.interner.intern_static("ref");
        let ref_mod_id = env.magic_core_submodule(ref_).unwrap();
        let ref_mod = env.get_module(ref_mod_id);

        for (sym, item) in ref_mod.items.clone() {
            let name = env.interner.resolve(sym).unwrap();
            let (_vis, _span, res) = item.spread();

            let res_value = env.get_res(res);

            eprintln!("{} ({:?})\n{:?}\n\n", name, res, res_value);
        }

        dbg![lower_errors];
        panic!();
    }
}
