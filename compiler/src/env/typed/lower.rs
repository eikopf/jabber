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
    hash::Hash,
    sync::Arc,
};

use crate::{
    ast::typed::{Bound, Name},
    env::{
        ModId, TermId, TypeId,
        resolve::{BoundResult, ResEnv},
    },
    symbol::Symbol,
    unique::Uid,
};

use crate::{
    ast::{bound, typed as ast},
    env::{Term, Type},
    span::Spanned,
};

use super::{TyVar, TypingError};

pub type LoweredType<V = Uid> = Type<Spanned<ast::Type<V>>>;
pub type TermTypeMap<V = Uid> = HashMap<TermId, Arc<ast::Ty<V>>>;
pub type LowerPassData<V = Uid> = (Vec<LoweredType<V>>, TermTypeMap<V>);

/// Collects the following type information from the given `env`:
/// 1. The lowered type declarations (field 0).
/// 2. The annotated type for each [`TermId`] (field 1).
/// 3. Any errors encountered (field 3).
pub fn try_collect_types(
    env: &ResEnv,
) -> Result<LowerPassData, Vec<TypingError>> {
    let types = try_lower_types(env)?;

    let mut errors = Vec::new();
    let mut term_types = HashMap::with_capacity(env.terms.len());

    for term_id in env.term_id_iter() {
        let Term { module, ast, .. } = env.get_term(term_id).as_ref();
        let mut ty_params = HashSet::new();
        let mut lowerer = TermLowerer::new(module, &mut ty_params, &mut errors);

        let ty = lowerer.get_annotated_ty(ast.item());
        term_types.insert(term_id, ty);
    }

    if errors.is_empty() {
        Ok((types, term_types))
    } else {
        Err(errors)
    }
}

/// Lowers the type declarations in the `env` to their typed representation.
/// This information is primarily used by [`try_collect_types()`].
pub fn try_lower_types(
    env: &ResEnv,
) -> Result<Vec<LoweredType>, Vec<TypingError>> {
    let mut errors = Vec::new();
    let mut types = Vec::with_capacity(env.types.len());

    for id in env.type_id_iter() {
        let Type { name, module, ast } = env.get_type(id).as_ref();
        let params: HashSet<_> =
            ast.params().iter().map(|binding| binding.id).collect();
        let mut lowerer = TypeLowerer::new(module, id, &params, &mut errors);

        let ast = lowerer.lower_type(ast.as_ref());
        types.push(Type { name, module, ast });
    }

    if errors.is_empty() {
        Ok(types)
    } else {
        Err(errors)
    }
}

pub struct TypeLowerer<'a> {
    module: ModId,
    id: TypeId,
    ty_params: &'a HashSet<Uid>,
    errors: &'a mut Vec<TypingError>,
}

impl<'a> TypeLowerer<'a> {
    pub fn new(
        module: ModId,
        id: TypeId,
        ty_params: &'a HashSet<Uid>,
        errors: &'a mut Vec<TypingError>,
    ) -> Self {
        Self {
            module,
            id,
            ty_params,
            errors,
        }
    }

    /// Projects a mutable reference to `self` into a [`TyReifier`].
    pub fn reifier(&mut self) -> TyReifier<'_> {
        TyReifier::new(self.module, Some(self.ty_params), self.errors)
    }

    pub fn lower_type(
        &mut self,
        Spanned { item, span }: Spanned<&bound::Type<BoundResult>>,
    ) -> Spanned<ast::Type> {
        let (attrs, name, params, kind) = match item {
            bound::Type::Alias(bound::TypeAlias {
                attrs,
                name,
                params,
                ty,
            }) => {
                // alias recursiveness check
                let mut recurrences = Vec::new();
                let mut finder = |inner_name: &BoundResult| {
                    if let Ok(bound) = inner_name.as_ref() {
                        if bound.as_res().is_some_and(|res| res == name.id) {
                            recurrences.push(bound.clone());
                        }
                    }
                };

                ty.item().for_each_name(&mut finder);

                for rec in recurrences {
                    let error = TypingError::RecursiveAliasRhs {
                        id: self.id,
                        occurrence: rec.span(),
                    };

                    self.errors.push(error);
                }

                let rhs_ty = {
                    let mut reifier = self.reifier();
                    let matrix = reifier.reify_ty_matrix(ty.as_ref());
                    reifier.quantify(matrix)
                };

                // alias rhs concreteness check
                if !rhs_ty.is_concrete() {
                    let error =
                        TypingError::NonConcreteAliasRhs { id: self.id };
                    self.errors.push(error);
                }

                // variable binding checks
                let bound_vars = rhs_ty.bound_vars().clone();
                self.check_bound_type_variables(params, bound_vars);

                (
                    attrs,
                    name,
                    params,
                    ast::TypeKind::Alias {
                        rhs_ast: ty.clone(),
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
                let constrs = self.lower_constructors(constructors, params);

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
                                .flat_map(|field| field.ty.matrix.vars())
                            {
                                bound_vars.insert(var);
                            }
                        }
                        ast::TyConstrKind::Tuple { elems, fn_ty: _ } => {
                            for var in
                                elems.iter().flat_map(|ty| ty.matrix.vars())
                            {
                                bound_vars.insert(var);
                            }
                        }
                    }
                }

                self.check_bound_type_variables(params, bound_vars);

                (
                    attrs,
                    name,
                    params,
                    ast::TypeKind::Adt {
                        opacity: *opacity,
                        constrs,
                    },
                )
            }
            bound::Type::Extern(bound::ExternType {
                attrs,
                name,
                params,
            }) => (attrs, name, params, ast::TypeKind::Extern),
        };

        span.with(ast::Type {
            attrs: attrs.clone(),
            name: *name,
            params: params.clone(),
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
                let error = TypingError::PhantomTypeParameter {
                    id: self.id,
                    param: *param,
                };

                self.errors.push(error);
            }

            let _ = bound_vars.remove(&param.id);
        }

        for var in bound_vars {
            let error = TypingError::UnboundTypeParameter {
                id: self.id,
                // the error printer will have to search for corresponding spans
                param_id: var,
            };

            self.errors.push(error);
        }
    }

    pub fn lower_constructors(
        &mut self,
        constrs: &HashMap<Symbol, Spanned<bound::TyConstr<BoundResult>>>,
        params: &[Name<Uid>],
    ) -> HashMap<Symbol, Spanned<ast::TyConstr>> {
        let (prefix, args) = {
            let mut prefix = HashSet::with_capacity(params.len());
            let mut args = Vec::with_capacity(params.len());

            for Name { id, .. } in params {
                prefix.insert(*id);
                args.push(Arc::new(ast::TyMatrix::Var(*id)));
            }

            (prefix, args.into_boxed_slice())
        };

        let matrix = Arc::new(ast::TyMatrix::Named {
            name: self.id,
            args,
        });

        let ty = Arc::new(ast::Ty {
            prefix: prefix.clone(),
            matrix: matrix.clone(),
        });

        constrs
            .iter()
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

                        // (un)quantify the component matrices
                        let elems: Box<[_]> = elem_matrices
                            .into_iter()
                            .map(ast::Ty::unquantified)
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
                                    let ty = ast::Ty::unquantified(matrix);

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

                let constr = ast.span.with(ast::TyConstr {
                    name,
                    kind,
                    ast: ast.clone(),
                });
                (*symbol, constr)
            })
            .collect()
    }
}

pub struct TermLowerer<'a> {
    module: ModId,
    ty_params: &'a mut HashSet<Uid>,
    errors: &'a mut Vec<TypingError>,
}

impl<'a> TermLowerer<'a> {
    pub fn new(
        module: ModId,
        ty_params: &'a mut HashSet<Uid>,
        errors: &'a mut Vec<TypingError>,
    ) -> Self {
        Self {
            module,
            ty_params,
            errors,
        }
    }

    /// Projects a mutable reference to `self` into a [`TyReifier`].
    pub fn reifier(&mut self) -> TyReifier<'_> {
        TyReifier::new(self.module, Some(self.ty_params), self.errors)
    }

    pub fn get_annotated_ty(
        &mut self,
        term: &bound::Term<BoundResult>,
    ) -> Arc<ast::Ty> {
        let mut reifier = self.reifier();
        let matrix = match term {
            bound::Term::Fn(bound::Fn {
                params, return_ty, ..
            }) => reifier.reify_fn_ty_annotation(
                params,
                return_ty.as_ref().map(Spanned::as_ref),
            ),
            bound::Term::ExternFn(bound::ExternFn {
                params,
                return_ty,
                ..
            }) => reifier.reify_fn_ty_annotation(
                params,
                return_ty.as_ref().map(Spanned::as_ref),
            ),
            bound::Term::Const(bound::Const { ty, .. }) => {
                reifier.reify_option_ty_matrix(ty.as_ref().map(Spanned::as_ref))
            }
        };

        reifier.quantify(matrix)
    }
}

// TYPE AST REIFICATION

pub struct TyReifier<'a, V = TyVar> {
    /// The current module.
    module: ModId,
    /// The type parameters in scope. If this is `None`, then type parameter
    /// checks are elided entirely.
    ty_params: Option<&'a HashSet<Uid>>,
    /// The universally quantified prefix of the reified type.
    prefix: HashSet<Uid>,
    /// The errors that occurred while reifying.
    errors: &'a mut Vec<TypingError<V>>,
}

impl<'a, V: Hash + Eq + Clone> TyReifier<'a, V> {
    /// Reifies a [`bound::Ty`] into an [`ast::TyMatrix`].
    pub fn reify_ty_matrix(
        &mut self,
        Spanned { span, item }: Spanned<&ast::TyAst<BoundResult>>,
    ) -> Arc<ast::TyMatrix> {
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
                match name.as_ref() {
                    Ok(Bound::Local(name)) => {
                        // if the id is known to be a type parameter but it has been
                        // used with arguments, this is an error
                        if self
                            .ty_params
                            .is_some_and(|params| params.contains(&name.id))
                            && !args.is_empty()
                        {
                            let error = TypingError::UsedTyParamAsPolytype {
                                param: *name,
                                module: self.module,
                                span,
                            };

                            self.errors.push(error);
                        }

                        // add the id to the prefix and return
                        self.prefix.insert(name.id);
                        ast::TyMatrix::Var(name.id)
                    }
                    // otherwise this is a named type, and we proceed as expected
                    Ok(
                        bound @ Bound::Path(Name { id, .. })
                        | bound @ Bound::Global(Name { id, .. }),
                    ) => {
                        match id.as_type() {
                            Some(name) => ast::TyMatrix::Named {
                                name,
                                args: args
                                    .iter()
                                    .map(|arg| {
                                        self.reify_ty_matrix(arg.as_ref())
                                    })
                                    .collect(),
                            },
                            None => {
                                // if id is not a TypeId, we emit an error and return garbage
                                let error = TypingError::BadResInNameTy {
                                    module: self.module,
                                    span: bound.span(),
                                    res: *id,
                                };
                                self.errors.push(error);
                                garbage_ty_matrix()
                            }
                        }
                    }
                    // if we get an error, throw an error! emit some garbage as well
                    Err(content) => {
                        let error = TypingError::UnresolvedName {
                            module: self.module,
                            name_content: content.clone(),
                        };
                        self.errors.push(error);
                        garbage_ty_matrix()
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
    ) -> Arc<ast::TyMatrix> {
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
    ) -> Arc<ast::TyMatrix> {
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
    pub fn quantify(self, matrix: Arc<ast::TyMatrix>) -> Arc<ast::Ty> {
        let Self { prefix, .. } = self;
        Arc::new(ast::Ty { prefix, matrix })
    }

    pub fn new(
        module: ModId,
        ty_params: Option<&'a HashSet<Uid>>,
        errors: &'a mut Vec<TypingError<V>>,
    ) -> Self {
        Self {
            module,
            ty_params,
            errors,
            prefix: Default::default(),
        }
    }
}

fn garbage_ty_matrix<V>() -> ast::TyMatrix<V> {
    ast::TyMatrix::Prim(ast::PrimTy::Never)
}
