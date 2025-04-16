//! Implementation for lowering into a typed environment and then checking
//! and inferring types within it.
//!
//! # Phases
//! Typechecking is broken into two phases,
//! 1. _lowering_, and;
//! 2. _checking_.
//!
//! ## Lowering
//! See the [`lower`] submodule.
//!
//! ## Checking
//! This is an (extended) implementation of _bidirectional typing_ as described
//! in the Dunfield & Krishnaswami papers (2013 and 2020). In particular, the
//! full 2013 paper and §5 from the 2020 paper are valuable for the polymorphic
//! elements of the type system, and the 2013 paper is authoritative on the
//! high-level implementation details.
//!
//! We proceed in two passes: first
//! 1. collection, and then;
//! 2. inference and unification.
//!
//! The first pass visits declarations (terms and types) but not their bodies,
//! reifying type annotations where possible and assigning fresh type variables
//! otherwise.
//!
//! The second pass infers the type of the body of each term, unifying with the
//! type obtained in the previous pass. These inferred types are then
//! generalized to make them properly generic.

use std::{collections::HashMap, hash::Hash, sync::Arc};

use ena::unify::{InPlace, UnificationTable, UnifyKey};
use lower::TyReifier;

use crate::{
    ast::{
        bound::{self, Bound, Name, NameContent},
        common::{ViSp, Vis},
        typed::{self as ast, Ty, TyMatrix, Typed},
    },
    env::{Env, Res, resolve::BoundResult},
    span::{Span, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

use super::{ModId, Term, TermId, Type, TypeId, resolve::ResEnv};

pub mod lower;

macro_rules! prim_ty {
    ($prim:expr) => {
        crate::ast::typed::Ty::unquantified(std::sync::Arc::new(
            crate::ast::typed::TyMatrix::Prim($prim),
        ))
    };
}

macro_rules! tyvar {
    ($var:expr) => {
        crate::ast::typed::Ty::unquantified(std::sync::Arc::new(
            crate::ast::typed::TyMatrix::Var($var),
        ))
    };
}

/// A typechecked [`Env`].
pub type TypedEnv = Env<
    Spanned<ast::Term<TyVar>>,
    Spanned<ast::Type<Uid>>,
    HashMap<Symbol, ViSp<Res>>,
>;

#[derive(Debug, Clone)]
pub enum TypingError<V = TyVar> {
    /// Found a non-type [`Res`] in a named type.
    BadResInNameTy {
        module: ModId,
        span: Span,
        res: Res,
    },
    UnresolvedName {
        module: ModId,
        name_content: Spanned<NameContent>,
    },
    DidNotUnify(Arc<TyMatrix<V>>, Arc<TyMatrix<V>>),
    OccursIn(V, Arc<TyMatrix<V>>),
    ExternFnTyIsNotConcrete {
        id: TermId,
        ty: Arc<Ty<V>>,
    },
    PubTermTyIsNotConcrete {
        id: TermId,
    },
    NonConcreteAliasRhs {
        id: TypeId,
    },
    RecursiveAliasRhs {
        id: TypeId,
        occurrence: Span,
    },
    UnboundTypeParameter {
        id: TypeId,
        param_id: Uid,
    },
    PhantomTypeParameter {
        id: TypeId,
        param: Name<Uid>,
    },
    UsedTyParamAsPolytype {
        param: Name<Uid>,
        span: Span,
        module: ModId,
    },
    TypeInNamePattern {
        id: TypeId,
        span: Span,
        module: ModId,
    },
    TermInNamePattern {
        id: TermId,
        span: Span,
        module: ModId,
    },
    NonUnitConstrInUnitConstrPattern {
        constr: ast::TyConstrIndex,
        span: Span,
        module: ModId,
    },
    /// Invalid constructor in a constructor pattern.
    BadConstrInConstrPattern {
        span: Span,
        module: ModId,
    },
    MissingRecordPatternFields {
        span: Span,
        module: ModId,
    },
    OpaqueTypeConstrPattern {
        constr: ast::TyConstrIndex,
        span: Span,
        module: ModId,
    },
    /// Used a record variant in an expression other than a record constructor expression.
    DirectRecordVariantExpr {
        constr: ast::TyConstrIndex,
        span: Span,
        module: ModId,
    },
    CalleeTyIsNotFn {
        callee_ty: Arc<Ty<TyVar>>,
        span: Span,
        module: ModId,
    },
    ArityMismatch {
        callee_arity: usize,
        arg_count: usize,
        callee_span: Span,
        span: Span,
        module: ModId,
    },
    LambdaArityMismatch {
        param_count: usize,
        expected_arity: usize,
        span: Span,
        module: ModId,
    },
    /// Expected a lambda expression to have a non-function type.
    ExpectedNonFnTyOfLambda {
        expected_ty: Arc<Ty<TyVar>>,
        span: Span,
        module: ModId,
    },
    /// The `name` in a RecordConstr expression could not be used as a type
    /// constructor.
    BadResInRecordConstrExpr {
        res: Res,
        span: Span,
        module: ModId,
    },
    /// Expected a record constructor in a record constructor expression but got
    /// a different kind of constructor.
    NotARecordConstr {
        constr: ast::TyConstrIndex,
        span: Span,
        module: ModId,
    },
    MissingRecordExprFields {
        constr: ast::TyConstrIndex,
        span: Span,
        module: ModId,
    },
    BadMutateLhs {
        lhs_span: Span,
        span: Span,
        module: ModId,
    },
    MutateLhsIsNotStruct {
        lhs_span: Span,
        span: Span,
        module: ModId,
    },
    MutateLhsIsNotRecordStruct {
        lhs_span: Span,
        span: Span,
        module: ModId,
    },
    NoSuchField {
        constr: ast::TyConstrIndex,
        field: Spanned<Symbol>,
        span: Span,
        module: ModId,
    },
    MutateLhsFieldIsImmutable {
        field: Symbol,
        lhs_span: Span,
        span: Span,
        module: ModId,
    },
    /// A tuple index occurred into non-tuple type.
    TupleIndexIntoBadTy {
        inferred_ty: Arc<Ty<TyVar>>,
        item_span: Span,
        span: Span,
        module: ModId,
    },
    TupleIndexOutOfBounds {
        item_length: usize,
        tuple_index: u32,
        item_span: Span,
        field_span: Span,
        span: Span,
        module: ModId,
    },
    /// The lhs of a record field expression was not a struct record type.    
    RecordFieldOfBadTy {
        inferred_ty: Arc<Ty<TyVar>>,
        item_span: Span,
        span: Span,
        module: ModId,
    },
    NoSuchRecordField {
        record: ast::TyConstrIndex,
        field: Symbol,
        item_span: Span,
        field_span: Span,
        span: Span,
        module: ModId,
    },
}

pub fn typecheck(
    mut env: ResEnv,
) -> Result<TypedEnv, (ResEnv, Vec<TypingError>)> {
    // first pass
    let (types, term_types) = match lower::try_collect_types(&env) {
        Ok((types, term_types)) => (types, term_types),
        Err(errors) => return Err((env, errors)),
    };

    let mut errors = Vec::new();

    // grab the list TypeId so we can use it in patterns
    let list_id = {
        let list_mod = env.interner.intern_static("list");
        let list_symbol = env.interner.intern_static("List");
        let list_mod_id = env.magic_core_submodule(list_mod).unwrap();
        let module = env.get_module(list_mod_id);
        module
            .items
            .get(&list_symbol)
            .unwrap()
            .item
            .item
            .as_type()
            .unwrap()
    };

    let first_module = env.terms.first().unwrap().module;
    let mut typer =
        Typer::new(&types, list_id, &term_types, &mut errors, first_module);
    typer.check_public_term_annotations(&env);

    // second pass
    let mut terms = Vec::with_capacity(env.terms.len());
    for term_id in env.term_id_iter() {
        let untyped_term = env.get_term(term_id).as_ref().map(Spanned::as_ref);

        match typer.type_term(term_id, untyped_term) {
            Ok(term) => terms.push(term),
            Err(error) => typer.errors.push(error),
        }
    }

    match errors.len() {
        0 => Ok(Env {
            types,
            terms,
            files: env.files,
            modules: env.modules,
            interner: env.interner,
            packages: env.packages,
        }),
        _ => Err((env, errors)),
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyVar(u32);

impl std::fmt::Debug for TyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "?{:?}", self.0)
    }
}

impl UnifyKey for TyVar {
    type Value = ();

    fn index(&self) -> u32 {
        self.0
    }

    fn from_index(u: u32) -> Self {
        Self(u)
    }

    fn tag() -> &'static str {
        "TyVar"
    }
}

type ExprResult<V = TyVar> =
    Result<Spanned<Typed<ast::Expr<V>, V>>, TypingError<V>>;

type TyResult<V = TyVar> = Result<Arc<Ty<V>>, TypingError<V>>;
type UnitResult<V = TyVar> = Result<(), TypingError<V>>;

pub struct Typer<'a> {
    /// The lowered type declarations.
    types: &'a [lower::LoweredType<Uid>],
    /// The [`TypeId`] of the core.list.List type.
    list_id: TypeId,
    /// A map from terms to their types.
    term_types: &'a lower::TermTypeMap<Uid>,
    /// Accumulated errors.
    errors: &'a mut Vec<TypingError>,
    /// Equivalence classes of [`TyVar`].
    unifier: UnificationTable<InPlace<TyVar>>,
    /// A mapping from type variables to types.
    var_assignments: HashMap<TyVar, Arc<TyMatrix<TyVar>>>,
    /// A mapping from [`Uid`] to [`TyVar`] in type expressions.
    uid_assigments: HashMap<Uid, TyVar>,
    /// The type judgements associated with local variables.
    local_var_types: HashMap<Uid, Arc<Ty<TyVar>>>,
    /// The current module.
    current_module: ModId,
}

impl<'a> Typer<'a> {
    pub fn new(
        types: &'a [lower::LoweredType],
        list_id: TypeId,
        term_types: &'a lower::TermTypeMap,
        errors: &'a mut Vec<TypingError>,
        current_module: ModId,
    ) -> Self {
        Self {
            types,
            list_id,
            term_types,
            errors,
            unifier: Default::default(),
            var_assignments: Default::default(),
            uid_assigments: Default::default(),
            local_var_types: Default::default(),
            current_module,
        }
    }

    /// Types the given term, returning `Some(..)` if and only if no errors
    /// occurred while typechecking.
    pub fn type_term(
        &mut self,
        id: TermId,
        Term { name, module, ast }: Term<Spanned<&bound::Term<BoundResult>>>,
    ) -> Result<Term<Spanned<ast::Term<TyVar>>>, TypingError> {
        // set current module
        self.current_module = module;

        // fetch and rebind annotated type
        let annotation = self.term_types.get(&id).cloned().unwrap();
        let annotated_ty = self.rebind(&annotation);

        let ast = ast.span.with(match ast.item() {
            bound::Term::Fn(bound::Fn {
                attrs,
                name,
                params,
                return_ty,
                body,
            }) => {
                let (domain, codomain) = annotated_ty.matrix.as_fn().unwrap();

                let params: Box<[_]> = params
                    .iter()
                    .zip(&domain)
                    .map(|(param, expected_ty)| {
                        let ty = Ty::unquantified(expected_ty.clone());
                        let pattern = self.check_pattern(
                            param.item.pattern.as_ref(),
                            ty.clone(),
                        )?;

                        self.unify_matrices(
                            ty.matrix.clone(),
                            expected_ty.clone(),
                        )?;

                        Ok(param.span.with(ast::Parameter {
                            pattern,
                            ty,
                            ty_ast: param.ty.clone(),
                        }))
                    })
                    .collect::<Result<_, _>>()?;

                let body = self.infer(body.as_ref().as_ref())?;
                self.unify_matrices(body.ty.matrix.clone(), codomain.clone())?;
                let body = self.zonk_spty(body);

                let ty = self.zonk(&Ty::unquantified(Arc::new(TyMatrix::Fn {
                    domain,
                    codomain,
                })));

                let ty = self.generalize(ty);

                ast::Term {
                    attrs: attrs.clone(),
                    name: *name,
                    ty,
                    kind: ast::TermKind::Fn {
                        params,
                        return_ty_ast: return_ty.clone(),
                        body,
                    },
                }
            }
            bound::Term::ExternFn(bound::ExternFn {
                attrs,
                name,
                params,
                return_ty,
            }) => {
                let params = self.lower_params(params)?;
                let ty = annotated_ty;

                if !ty.is_concrete() {
                    let ty = ty.clone();
                    Err(TypingError::ExternFnTyIsNotConcrete { id, ty })?;
                }

                ast::Term {
                    attrs: attrs.clone(),
                    name: *name,
                    ty,
                    kind: ast::TermKind::ExternFn {
                        params,
                        return_ty_ast: return_ty.clone(),
                    },
                }
            }
            bound::Term::Const(bound::Const {
                attrs,
                name,
                ty: ty_ast,
                value,
            }) => {
                let value = self.infer(value.as_ref())?;
                self.unify(value.ty.clone(), annotated_ty.clone())?;
                let value = self.zonk_spty(value);

                ast::Term {
                    attrs: attrs.clone(),
                    name: *name,
                    ty: self.zonk(&annotated_ty),
                    kind: ast::TermKind::Const {
                        ty_ast: ty_ast.clone(),
                        value,
                    },
                }
            }
        });

        Ok(Term { name, module, ast })
    }

    pub fn typecheck_expr(
        &mut self,
        expr: Spanned<&bound::Expr<BoundResult>>,
    ) -> ExprResult {
        self.infer(expr)
    }

    pub fn check(
        &mut self,
        Spanned { item, span }: Spanned<&bound::Expr<BoundResult>>,
        expected_ty: Arc<Ty<TyVar>>,
    ) -> ExprResult {
        match item {
            bound::Expr::Lambda { params, body } => {
                let fn_ty = self.rebind(&Ty::fresh_unbound_fn(params.len()));
                self.unify(expected_ty.clone(), fn_ty.clone())?;
                let expected_ty = self.zonk(&expected_ty);
                let (domain, codomain) = expected_ty.matrix.as_fn().unwrap();

                // convert domain into a unit domain if necessary
                let domain = match domain.as_ref() {
                    [] => vec![Arc::new(TyMatrix::Prim(ast::PrimTy::Unit))]
                        .into_boxed_slice(),
                    _ => domain,
                };

                // check the parameters against the domain
                let params = self.check_params(
                    params,
                    domain.iter().cloned().map(Ty::unquantified),
                )?;

                // check whether the unit syntax sugar applies
                let unit_sugar = is_unit_domain(&domain)
                    && match params.as_ref() {
                        [] | [_, _, ..] => true,
                        [param] => param.pattern.is_unit(),
                    };

                // check arity
                if !unit_sugar && params.len() != domain.len() {
                    return Err(TypingError::LambdaArityMismatch {
                        param_count: params.len(),
                        expected_arity: domain.len(),
                        span,
                        module: self.module(),
                    });
                }

                // if the unit syntax sugar doesn't apply, check parameter types
                // against the domain elementwise
                if !unit_sugar {
                    for (param, ty) in params.iter().zip(&domain) {
                        self.unify_matrices(
                            param.ty.matrix.clone(),
                            ty.clone(),
                        )?;
                    }
                }

                // check the body against the codomain
                let body = Box::new(self.check(
                    body.as_ref().as_ref(),
                    Ty::unquantified(codomain.clone()),
                )?);

                // reassemble zonked body
                let body = Box::new(body.span.with(Typed {
                    ty: self.zonk(&body.ty),
                    item: body.item.item,
                }));

                // assemble function type
                let ty =
                    Ty::unquantified(self.zonk_matrix(Arc::new(
                        TyMatrix::Fn { domain, codomain },
                    )));

                Ok(span.with(ty.with(ast::Expr::Lambda { params, body })))
            }
            // inference mode rules
            expr => {
                let expr = self.infer(span.with(expr))?;
                self.unify(expr.ty.clone(), expected_ty.clone())?;
                Ok(self.zonk_spty(expr))
            }
        }
    }

    pub fn infer(
        &mut self,
        Spanned { item, span }: Spanned<&bound::Expr<BoundResult>>,
    ) -> ExprResult {
        match item {
            bound::Expr::Name(name) => match name.as_ref() {
                Ok(Bound::Local(name @ Name { id, .. })) => {
                    let ty = match self.local_var_types.get(id) {
                        Some(ty) => {
                            Ty::unquantified(self.instantiate(&ty.clone()))
                        }
                        None => {
                            let ty = tyvar!(self.fresh_var());
                            self.local_var_types.insert(*id, ty.clone());
                            ty
                        }
                    };

                    let ty = self.zonk(&ty);
                    Ok(span.with(ty.with(ast::Expr::Local(*name))))
                }
                Ok(
                    bound @ Bound::Global(Name { id, .. })
                    | bound @ Bound::Path(Name { id, .. }),
                ) => {
                    let ty = self.lookup_res(*id, (span, self.module()))?;
                    Ok(span.with(ty.with(ast::Expr::Global(Name {
                        id: *id,
                        content: bound.clone().content(),
                    }))))
                }
                Err(content) => Err(TypingError::UnresolvedName {
                    module: self.module(),
                    name_content: content.clone(),
                }),
            },
            bound::Expr::Literal(literal) => {
                let Typed { item, ty } = self.infer_literal(span.with(literal));
                let expr = ast::Expr::Literal(item.item);
                Ok(span.with(ty.with(expr)))
            }
            bound::Expr::Tuple(elems) => {
                let tys: Box<_> = std::iter::repeat_with(|| {
                    Arc::new(TyMatrix::Var(self.fresh_var()))
                })
                .take(elems.len())
                .collect();

                let elems = elems
                    .iter()
                    .map(Spanned::as_ref)
                    .zip(&tys)
                    .try_fold(vec![], |mut elems, (elem, ty)| {
                        let elem =
                            self.check(elem, Ty::unquantified(ty.clone()))?;
                        let elem =
                            elem.map(|elem| elem.map_ty(|ty| self.zonk(&ty)));
                        elems.push(elem);
                        Ok(elems)
                    })?
                    .into_boxed_slice();

                let tuple = self.zonk_matrix(Arc::new(TyMatrix::Tuple(tys)));
                let ty = Ty::unquantified(tuple);
                Ok(span.with(ty.with(ast::Expr::Tuple(elems))))
            }
            bound::Expr::List(elems) => {
                let ty = tyvar!(self.fresh_var());

                // check each element
                let elems: Box<_> = elems
                    .iter()
                    .map(Spanned::as_ref)
                    .map(|elem| self.check(elem, ty.clone()))
                    .collect::<Result<_, _>>()?;

                // zonk the elements in a second pass
                let elems = elems
                    .into_iter()
                    .map(|elem| {
                        elem.map(|elem| elem.map_ty(|ty| self.zonk(&ty)))
                    })
                    .collect();

                let ty = Ty::unquantified(Arc::new(TyMatrix::Named {
                    name: self.list_id,
                    args: vec![self.zonk_matrix(ty.matrix.clone())]
                        .into_boxed_slice(),
                }));

                Ok(span.with(ty.with(ast::Expr::List(elems))))
            }
            bound::Expr::Block(bound::Block {
                statements,
                return_expr,
            }) => {
                let statements = statements
                    .iter()
                    .map(Spanned::as_ref)
                    .try_fold(vec![], |mut stmts, Spanned { item, span }| {
                        match item {
                            bound::Stmt::Empty => (),
                            bound::Stmt::Expr(expr) => {
                                let expr = self.infer(span.with(expr))?.item;
                                let stmt = span.with(ast::Stmt::Expr(expr));
                                stmts.push(stmt);
                            }
                            bound::Stmt::Let { pattern, ty, value } => {
                                // infer type of value
                                let value = self.infer(value.as_ref())?;

                                // reify annotation
                                let annotation = {
                                    let mut reifier = self.reifier();
                                    let matrix = reifier
                                        .reify_option_ty_matrix(
                                            ty.as_ref().map(Spanned::as_ref),
                                        );
                                    let ty = reifier.quantify(matrix);
                                    self.rebind(&ty)
                                };

                                // check value against annotation
                                self.unify(
                                    value.ty.clone(),
                                    annotation.clone(),
                                )?;

                                // let-generalize
                                let value = {
                                    let span = value.span();
                                    let ty = self.zonk(&value.ty);
                                    let ty = self.generalize(ty);
                                    span.with(ty.with(value.item.item))
                                };

                                // lower pattern and bind in the environment
                                let pattern = self.check_pattern(
                                    pattern.as_ref(),
                                    value.ty.clone(),
                                )?;

                                stmts.push(
                                    span.with(ast::Stmt::Let {
                                        pattern,
                                        value,
                                    }),
                                );
                            }
                        }

                        Ok(stmts)
                    })?
                    .into_boxed_slice();

                let return_expr = return_expr
                    .as_ref()
                    .map(|expr| self.infer(expr.as_ref().as_ref()))
                    .transpose()?
                    .map(Box::new);

                let ty = return_expr
                    .as_ref()
                    .map(|expr| self.zonk(&expr.ty))
                    .unwrap_or_else(|| prim_ty!(ast::PrimTy::Unit));

                Ok(span.with(ty.with(ast::Expr::Block {
                    statements,
                    return_expr,
                })))
            }
            bound::Expr::RecordConstr { name, fields, base } => {
                // unwrap name
                let name = self.try_get_bound_ref(name)?;

                // get constructor
                let constr_id = match name.as_res().unwrap() {
                    Res::StructType(ty) => {
                        let name = self.get_type(ty).name;
                        Ok(ast::TyConstrIndex { ty, name })
                    }
                    Res::TyConstr { ty, name } => {
                        Ok(ast::TyConstrIndex { ty, name })
                    }
                    res => Err(TypingError::BadResInRecordConstrExpr {
                        res,
                        span,
                        module: self.module(),
                    }),
                }?;

                // grab constructor data
                let constr = self.lookup_constr(constr_id);
                let constr_fields = match &constr.kind {
                    ast::TyConstrKind::Record(fields) => Ok(fields.clone()),
                    _ => Err(TypingError::NotARecordConstr {
                        constr: constr_id,
                        span,
                        module: self.module(),
                    }),
                }?;

                // check for field coverage
                if base.is_none() && constr_fields.len() != fields.len() {
                    return Err(TypingError::MissingRecordExprFields {
                        constr: constr_id,
                        span,
                        module: self.module(),
                    });
                }

                // instantiate the type and the constructor's fields
                let (constr_fields, args) = {
                    let params = self.get_ty_params(constr_id.ty);
                    let (args, mut subst) =
                        self.make_param_instantiation(params);
                    let constr_fields: HashMap<_, _> = constr_fields
                        .into_iter()
                        .map(|(name, field)| {
                            (
                                name,
                                ast::RecordField {
                                    mutability: field.mutability,
                                    name: field.name,
                                    ty: Ty::unquantified(subst(
                                        field.ty.matrix.clone(),
                                    )),
                                },
                            )
                        })
                        .collect();

                    (constr_fields, args)
                };

                // check the fields
                let fields = fields
                    .iter()
                    .map(Spanned::as_ref)
                    .try_fold(vec![], |mut fields, Spanned { item, span }| {
                        let field = item.field;
                        let ty = constr_fields.get(&field).unwrap().ty.clone();

                        let value = self
                            .check(item.value.as_ref(), ty)?
                            .map(|value| value.map_ty(|ty| self.zonk(&ty)));

                        let field =
                            span.with(ast::RecordExprField { field, value });
                        fields.push(field);
                        Ok(fields)
                    })?
                    .into_boxed_slice();

                // assemble inferred type
                let ty = Ty::unquantified(Arc::new(TyMatrix::Named {
                    name: constr_id.ty,
                    args,
                }));

                // check base expr against inferred type
                let base = base
                    .as_ref()
                    .map(|base| self.check(base.as_ref().as_ref(), ty.clone()))
                    .transpose()?
                    .map(Box::new);

                Ok(span.with(ty.with(ast::Expr::RecordConstr {
                    name: name.clone(),
                    fields,
                    base,
                })))
            }
            bound::Expr::RecordField { item, field } => {
                let item = self.infer(item.as_ref().as_ref())?;

                let ty = match item.ty.matrix.as_ref() {
                    TyMatrix::Named { name, args } => {
                        let type_ = self.get_type(*name);
                        let params = self.get_ty_params(*name);

                        // sanity check
                        assert_eq!(args.len(), params.len());

                        // assemble {params -> args} substitution
                        let subst = params
                            .into_iter()
                            .zip(args.iter().cloned())
                            .collect::<HashMap<_, _>>();

                        match type_.ast.as_struct_constr() {
                            Some(constr) if constr.is_record() => {
                                let fields =
                                    constr.kind.as_record_fields().unwrap();

                                match fields.get(field).cloned() {
                                    Some(field) => {
                                        let ty = self.rebind_with(
                                            Arc::unwrap_or_clone(field.ty),
                                            &subst,
                                        );

                                        Ok(self.zonk(&ty))
                                    }
                                    None => {
                                        Err(TypingError::NoSuchRecordField {
                                            record: ast::TyConstrIndex {
                                                ty: *name,
                                                name: constr.name.item,
                                            },
                                            field: field.item,
                                            item_span: item.span(),
                                            field_span: field.span(),
                                            span,
                                            module: self.module(),
                                        })
                                    }
                                }
                            }
                            _ => Err(TypingError::RecordFieldOfBadTy {
                                inferred_ty: self.zonk(&item.ty),
                                item_span: item.span(),
                                span,
                                module: self.module(),
                            }),
                        }
                    }
                    _ => Err(TypingError::RecordFieldOfBadTy {
                        inferred_ty: self.zonk(&item.ty),
                        item_span: item.span(),
                        span,
                        module: self.module(),
                    }),
                }?;

                let item = Box::new(self.zonk_spty(item));
                let field = *field;

                Ok(span.with(ty.with(ast::Expr::RecordField { item, field })))
            }
            bound::Expr::TupleField { item, field } => {
                // infer item type
                let item = self.infer(item.as_ref().as_ref())?;

                // unwrap field (panics if the field overflowed)
                let field = field
                    .as_ref()
                    .map(|index| index.as_ref().copied().unwrap());

                // extract the field type
                let ty = match item.ty.matrix.as_ref() {
                    TyMatrix::Tuple(elems) => {
                        match elems.get(*field as usize) {
                            Some(ty) => {
                                let prefix = item.ty.prefix.clone();
                                let matrix = ty.clone();
                                Ok(self.zonk(&Ty { prefix, matrix }))
                            }
                            None => Err(TypingError::TupleIndexOutOfBounds {
                                item_length: elems.len(),
                                tuple_index: field.item,
                                item_span: item.span(),
                                field_span: field.span(),
                                span,
                                module: self.module(),
                            }),
                        }
                    }
                    TyMatrix::Named { name, args } => {
                        let type_ = self.get_type(*name);
                        let params = self.get_ty_params(*name);

                        // sanity check
                        assert_eq!(args.len(), params.len());

                        let subst = params
                            .into_iter()
                            .zip(args.iter().cloned())
                            .collect::<HashMap<_, _>>();

                        match type_.ast.as_struct_constr() {
                            Some(constr) if constr.is_tuple() => {
                                // safe dirty unwrap
                                let elems =
                                    constr.kind.as_tuple_elems().unwrap();

                                match elems.get(*field as usize).cloned() {
                                    Some(ty) => {
                                        // instantiate type
                                        let ty = self.rebind_with(
                                            Arc::unwrap_or_clone(ty),
                                            &subst,
                                        );

                                        Ok(self.zonk(&ty))
                                    }
                                    None => Err(
                                        TypingError::TupleIndexOutOfBounds {
                                            item_length: elems.len(),
                                            tuple_index: field.item,
                                            item_span: item.span(),
                                            field_span: field.span(),
                                            span,
                                            module: self.module(),
                                        },
                                    ),
                                }
                            }
                            _ => Err(TypingError::TupleIndexIntoBadTy {
                                inferred_ty: item.ty.clone(),
                                item_span: item.span(),
                                span,
                                module: self.module(),
                            }),
                        }
                    }
                    _ => Err(TypingError::TupleIndexIntoBadTy {
                        inferred_ty: item.ty.clone(),
                        item_span: item.span(),
                        span,
                        module: self.module(),
                    }),
                }?;

                let item = Box::new(self.zonk_spty(item));
                Ok(span.with(ty.with(ast::Expr::TupleField { item, field })))
            }
            bound::Expr::Call { callee, args, kind } => {
                // infer callee type
                let callee = self.infer(callee.as_ref().as_ref())?;

                // unify to ensure we have a function type with the right arity
                let fn_ty = self.rebind(&Ty::fresh_unbound_fn(args.len()));
                self.unify(fn_ty, callee.ty.clone())?;

                // check if the callee is a function or not
                let (domain, codomain) = self
                    .zonk_matrix(callee.ty.matrix.clone())
                    .as_fn()
                    .ok_or(TypingError::CalleeTyIsNotFn {
                        callee_ty: callee.ty.clone(),
                        span: callee.span,
                        module: self.module(),
                    })?;

                // empty domains are converted to unary unit domains
                let domain = match domain.as_ref() {
                    [] => vec![Arc::new(TyMatrix::Prim(ast::PrimTy::Unit))]
                        .into_boxed_slice(),
                    _ => domain,
                };

                // empty arguments are converted to single unit arguments
                let args =
                    match args.as_ref() {
                        [] => vec![callee.span.with(bound::Expr::Literal(
                            bound::LiteralExpr::Unit,
                        ))]
                        .into_boxed_slice(),
                        _ => args.clone(),
                    };

                // check arguments against the inferred domain
                let args = args
                    .into_iter()
                    .zip(domain)
                    .try_fold(vec![], |mut args, (arg, ty)| {
                        let arg =
                            self.check(arg.as_ref(), Ty::unquantified(ty))?;
                        args.push(arg);
                        Ok(args)
                    })?
                    .into_boxed_slice();

                let callee = Box::new(self.zonk_spty(callee));
                let kind = *kind;
                let ty = Ty::unquantified(self.zonk_matrix(codomain));
                Ok(span.with(ty.with(ast::Expr::Call { callee, args, kind })))
            }
            bound::Expr::LazyAnd { operator, lhs, rhs } => {
                // rewrite operator
                let operator = operator.with(ast::LazyOperator::And);

                // infer subexpressions
                let lhs = self.infer(lhs.as_ref().as_ref())?;
                let rhs = self.infer(rhs.as_ref().as_ref())?;

                // we know the inferred type to be `bool`
                let ty = prim_ty!(ast::PrimTy::Bool);
                self.unify(lhs.ty.clone(), ty.clone())?;
                self.unify(rhs.ty.clone(), ty.clone())?;

                // zonk subexpressions
                let lhs = Box::new(self.zonk_spty(lhs));
                let rhs = Box::new(self.zonk_spty(rhs));

                Ok(span.with(ty.with(ast::Expr::Lazy { operator, lhs, rhs })))
            }
            bound::Expr::LazyOr { operator, lhs, rhs } => {
                let operator = operator.with(ast::LazyOperator::Or);

                // infer subexpressions
                let lhs = self.infer(lhs.as_ref().as_ref())?;
                let rhs = self.infer(rhs.as_ref().as_ref())?;

                // we know the inferred type to be `bool`
                let ty = prim_ty!(ast::PrimTy::Bool);
                self.unify(lhs.ty.clone(), ty.clone())?;
                self.unify(rhs.ty.clone(), ty.clone())?;

                // zonk subexpressions
                let lhs = Box::new(self.zonk_spty(lhs));
                let rhs = Box::new(self.zonk_spty(rhs));

                Ok(span.with(ty.with(ast::Expr::Lazy { operator, lhs, rhs })))
            }
            bound::Expr::Mutate { operator, lhs, rhs } => {
                // extract the lhs as a record field expression
                let (item, field) = match lhs.item() {
                    bound::Expr::RecordField { item, field } => {
                        Ok((item.as_ref().as_ref(), *field))
                    }
                    _ => Err(TypingError::BadMutateLhs {
                        lhs_span: lhs.span(),
                        span,
                        module: self.module(),
                    }),
                }?;

                // infer the item type
                let item = Box::new(self.infer(item)?);

                // extract the named TypeId and the field definition
                let (id, args, field_def) = match item.ty.matrix.as_ref() {
                    TyMatrix::Named { name, args } => {
                        let ty = self.get_type(*name);

                        match ty.ast.as_struct_constr() {
                            Some(constr) => match &constr.kind {
                                ast::TyConstrKind::Record(fields) => {
                                    let field = fields.get(&field).ok_or_else(
                                        || TypingError::NoSuchField {
                                            constr: ast::TyConstrIndex {
                                                ty: *name,
                                                name: field.item,
                                            },
                                            field,
                                            span,
                                            module: self.module(),
                                        },
                                    )?;

                                    Ok((*name, args.clone(), field.clone()))
                                }
                                _ => Err(
                                    TypingError::MutateLhsIsNotRecordStruct {
                                        lhs_span: lhs.span(),
                                        span,
                                        module: self.module(),
                                    },
                                ),
                            },
                            None => Err(TypingError::MutateLhsIsNotStruct {
                                lhs_span: lhs.span(),
                                span,
                                module: self.module(),
                            }),
                        }
                    }
                    _ => Err(TypingError::MutateLhsIsNotStruct {
                        lhs_span: lhs.span(),
                        span,
                        module: self.module(),
                    }),
                }?;

                // check if the field is mutable (non-fatal error for typing)
                if field_def.mutability.is_none() {
                    self.errors.push(TypingError::MutateLhsFieldIsImmutable {
                        field: field.item,
                        lhs_span: lhs.span(),
                        span,
                        module: self.module(),
                    });
                }

                // instantiate field type
                let field_ty = {
                    let params = self.get_ty_params(id);
                    assert_eq!(params.len(), args.len());

                    let subst: HashMap<_, _> =
                        params.into_iter().zip(args).collect();

                    let mut rebinder = |&var: &Uid| self.get_or_assign_var(var);
                    Ty::unquantified(apply_substitution(
                        &subst,
                        field_def.ty.matrix.clone(),
                        &mut rebinder,
                    ))
                };

                // check the rhs
                let rhs = Box::new(
                    self.check(rhs.as_ref().as_ref(), field_ty.clone())?,
                );

                // infer the unit type
                let ty = prim_ty!(ast::PrimTy::Unit);

                Ok(span.with(ty.with(ast::Expr::Mutate {
                    operator: *operator,
                    item,
                    field,
                    rhs,
                })))
            }
            bound::Expr::Match { scrutinee, arms } => {
                // infer scrutinee type
                let scrutinee =
                    Box::new(self.infer(scrutinee.as_ref().as_ref())?);

                // make fresh return type
                let ty =
                    Ty::unquantified(Arc::new(TyMatrix::Var(self.fresh_var())));

                // check match arms
                let arms = arms
                    .iter()
                    .map(Spanned::as_ref)
                    .try_fold(vec![], |mut arms, Spanned { item, span }| {
                        let pattern = self.check_pattern(
                            item.pattern.as_ref(),
                            scrutinee.ty.clone(),
                        )?;

                        let body =
                            self.check(item.body.as_ref(), ty.clone())?;

                        arms.push(span.with(ast::MatchArm { pattern, body }));
                        Ok(arms)
                    })?
                    .into_boxed_slice();

                Ok(span.with(ty.with(ast::Expr::Match { scrutinee, arms })))
            }
            bound::Expr::IfElse {
                condition,
                consequence,
                alternative,
            } => {
                // check the condition is a boolean
                let condition = self.check(
                    condition.as_ref().as_ref(),
                    prim_ty!(ast::PrimTy::Bool),
                )?;

                // rewrite the consequence and alternative into expressions
                let consequence = consequence
                    .span
                    .with(bound::Expr::Block(consequence.item.clone()));
                let alternative = alternative.as_ref().map(|block| {
                    block.span.with(bound::Expr::Block(block.item.clone()))
                });

                // pick a unification starting point
                let ty = match alternative.as_ref() {
                    Some(_) => tyvar!(self.fresh_var()),
                    None => prim_ty!(ast::PrimTy::Unit),
                };

                // check branches
                let consequence =
                    self.check(consequence.as_ref(), ty.clone())?;
                let alternative = alternative
                    .map(|expr| self.check(expr.as_ref(), ty.clone()))
                    .transpose()?;

                // rewrite this expression into a match expression
                let scrutinee = Box::new(condition);

                let arms = {
                    let consequence = consequence.span.with(ast::MatchArm {
                        pattern: consequence.span.with(ast::Pattern::Literal(
                            ast::LiteralExpr::Bool(true),
                        )),
                        body: consequence,
                    });

                    let span =
                        alternative.as_ref().map(Spanned::span).unwrap_or(span);

                    let alternative = span.with(ast::MatchArm {
                        pattern: span.with(ast::Pattern::Literal(
                            ast::LiteralExpr::Bool(false),
                        )),
                        body: alternative.unwrap_or_else(|| {
                            let ty = prim_ty!(ast::PrimTy::Unit);
                            span.with(ty.with(ast::Expr::Literal(
                                ast::LiteralExpr::Unit,
                            )))
                        }),
                    });

                    vec![consequence, alternative].into_boxed_slice()
                };

                let ty = self.zonk(&ty);
                Ok(span.with(ty.with(ast::Expr::Match { scrutinee, arms })))
            }
            // check mode rules
            expr => {
                let ty = tyvar!(self.fresh_var());
                let expr = self.check(span.with(expr), ty)?;
                Ok(self.zonk_spty(expr))
            }
        }
    }

    pub fn unify(
        &mut self,
        t1: Arc<Ty<TyVar>>,
        t2: Arc<Ty<TyVar>>,
    ) -> UnitResult {
        self.unify_matrices(t1.matrix.clone(), t2.matrix.clone())
    }

    fn unify_matrices(
        &mut self,
        t1: Arc<TyMatrix<TyVar>>,
        t2: Arc<TyMatrix<TyVar>>,
    ) -> UnitResult {
        let t1 = self.normalize(&t1).unwrap();
        let t2 = self.normalize(&t2).unwrap();

        match (t1.as_ref(), t2.as_ref()) {
            // variable-variable
            (TyMatrix::Var(v1), TyMatrix::Var(v2)) => {
                self.unifier.union(*v1, *v2);
                Ok(())
            }

            // value-variable & variable-value
            (_, TyMatrix::Var(var)) => self.unify_var_value(*var, t1),
            (TyMatrix::Var(var), _) => self.unify_var_value(*var, t2),

            // never coercion
            (TyMatrix::Prim(ast::PrimTy::Never), _)
            | (_, TyMatrix::Prim(ast::PrimTy::Never)) => Ok(()),

            // identical primitives
            (TyMatrix::Prim(p1), TyMatrix::Prim(p2)) if p1 == p2 => Ok(()),

            // equal-length tuples
            (TyMatrix::Tuple(elems1), TyMatrix::Tuple(elems2))
                if elems1.len() == elems2.len() =>
            {
                for (l, r) in elems1.iter().zip(elems2) {
                    self.unify_matrices(l.clone(), r.clone())?;
                }

                Ok(())
            }

            // function-function
            (
                TyMatrix::Fn {
                    domain: d1,
                    codomain: c1,
                },
                TyMatrix::Fn {
                    domain: d2,
                    codomain: c2,
                },
            ) => {
                // we need to check that either
                // 1. d1.len() == d2.len(), or;
                // 2. d1 and d2 can both be treated as unit domains.

                if d1.len() == d2.len() {
                    for (l, r) in d1.iter().zip(d2) {
                        self.unify_matrices(l.clone(), r.clone())?;
                    }

                    self.unify_matrices(c1.clone(), c2.clone())
                } else if is_unit_domain(d1) && is_unit_domain(d2) {
                    self.unify_matrices(c1.clone(), c2.clone())
                } else {
                    Err(TypingError::DidNotUnify(t1, t2))
                }
            }

            // named-named
            (
                TyMatrix::Named { name: n1, args: a1 },
                TyMatrix::Named { name: n2, args: a2 },
            ) => {
                // we presume the inputs to be normalized, i.e. aliases have been fully expanded.
                if n1 == n2 && a1.len() == a2.len() {
                    for (l, r) in a1.iter().zip(a2) {
                        self.unify_matrices(l.clone(), r.clone())?;
                    }

                    Ok(())
                } else {
                    Err(TypingError::DidNotUnify(t1, t2))
                }
            }
            _ => Err(TypingError::DidNotUnify(t1, t2)),
        }
    }

    fn lookup_res(&mut self, res: Res, blame: (Span, ModId)) -> TyResult {
        match res {
            Res::Term(id) => {
                // all terms are lowered, so this unwrap is fine (if gross)
                let ty = self.term_types.get(&id).unwrap();
                Ok(Ty::unquantified(self.instantiate_uid(ty)))
            }
            Res::TyConstr { ty, name } => {
                let constr = ast::TyConstrIndex { ty, name };
                self.get_ty_constr_type(constr, blame)
            }
            Res::StructType(ty) => {
                let name = self.get_type(ty).name;
                let constr = ast::TyConstrIndex { ty, name };
                self.get_ty_constr_type(constr, blame)
            }
            _ => panic!("a name was bound to a module or type"),
        }
    }

    fn get_ty_constr_type(
        &mut self,
        constr: ast::TyConstrIndex,
        blame: (Span, ModId),
    ) -> TyResult {
        match self.lookup_constr(constr).get_ty().cloned() {
            Some(ty) => Ok(self.rebind(&ty)),
            None => Err(TypingError::DirectRecordVariantExpr {
                constr,
                span: blame.0,
                module: blame.1,
            }),
        }
    }

    /// Lowers a list of parameters, checks them against their annotated types,
    /// and adds the types of any variables into the environment.
    fn lower_params(
        &mut self,
        params: &[Spanned<bound::Parameter<BoundResult>>],
    ) -> Result<SpanSeq<ast::Parameter<TyVar>>, TypingError> {
        let mut typed_params = Vec::with_capacity(params.len());

        for Spanned { span, item } in params.iter().map(Spanned::as_ref) {
            let bound::Parameter {
                pattern,
                ty: ty_ast,
            } = item;

            let ty = {
                let mut reifier = self.reifier();
                let matrix = reifier.reify_option_ty_matrix(
                    ty_ast.as_ref().map(Spanned::as_ref),
                );
                let uid_ty = reifier.quantify(matrix);

                let ty = self.rebind(&uid_ty);
                self.zonk(&ty)
            };

            let pattern = self.check_pattern(pattern.as_ref(), ty.clone())?;
            let ty = self.zonk(&ty);

            let pat = ast::Parameter {
                pattern,
                ty,
                ty_ast: ty_ast.clone(),
            };

            typed_params.push(span.with(pat));
        }

        Ok(typed_params.into_boxed_slice())
    }

    fn check_params(
        &mut self,
        params: &[Spanned<bound::Parameter<BoundResult>>],
        tys: impl IntoIterator<Item = Arc<Ty<TyVar>>>,
    ) -> Result<SpanSeq<ast::Parameter<TyVar>>, TypingError> {
        // if there are no params, we have () -> ... or fn foo() = ...
        if params.is_empty() {
            // check that there's only one ty and grab it
            let mut ty_iter = tys.into_iter();
            let ty = ty_iter.next().unwrap();
            assert!(ty_iter.next().is_none());

            // unify with the unit type
            self.unify(ty, prim_ty!(ast::PrimTy::Unit))?;

            // return an empty list of parameters
            return Ok(Default::default());
        }

        params
            .iter()
            .map(Spanned::as_ref)
            .zip(tys)
            .map(|(Spanned { item: param, span }, ty)| {
                let annotated_ty = {
                    let mut reifier = self.reifier();
                    let matrix = reifier.reify_option_ty_matrix(
                        param.ty.as_ref().map(Spanned::as_ref),
                    );

                    let matrix = self.rebind_matrix(&matrix);
                    Ty::unquantified(matrix)
                };

                let pattern = self.check_pattern(
                    param.pattern.as_ref(),
                    annotated_ty.clone(),
                )?;

                self.unify(annotated_ty.clone(), ty)?;

                let ty = self.zonk(&annotated_ty);

                Ok(span.with(ast::Parameter {
                    pattern,
                    ty,
                    ty_ast: param.ty.clone(),
                }))
            })
            .collect::<Result<_, _>>()
    }

    fn check_pattern(
        &mut self,
        Spanned { item, span }: Spanned<&bound::Pattern<BoundResult>>,
        ty: Arc<Ty<TyVar>>,
    ) -> Result<Spanned<ast::Pattern<TyVar>>, TypingError> {
        match item {
            bound::Pattern::Wildcard => Ok(span.with(ast::Pattern::Wildcard)),
            bound::Pattern::Literal(literal) => {
                let literal = self.infer_literal(span.with(literal));
                self.unify(literal.ty, ty)?;
                Ok(span.with(ast::Pattern::Literal(literal.item.item)))
            }
            bound::Pattern::Name(name) => match name {
                // if the name is a res, we check for unit constructors
                Ok(
                    bound @ Bound::Path(Name { id, .. })
                    | bound @ Bound::Global(Name { id, .. }),
                ) => {
                    let (constr, id) = match *id {
                        // regular constructors
                        Res::TyConstr { ty: id, name } => {
                            let id = ast::TyConstrIndex { ty: id, name };

                            let named_ty = {
                                let nparams =
                                    self.get_type(id.ty).ast.params.len();
                                let name = id.ty;

                                let args = std::iter::repeat_with(|| {
                                    Arc::new(TyMatrix::Var(self.fresh_var()))
                                })
                                .take(nparams)
                                .collect();

                                self.instantiate(&Ty::unquantified(Arc::new(
                                    TyMatrix::Named { name, args },
                                )))
                            };

                            self.unify_matrices(named_ty, ty.matrix.clone())?;

                            let ast = &self.get_type(id.ty).ast;
                            match &ast.kind {
                                ast::TypeKind::Adt { opacity, constrs } => {
                                    match opacity {
                                        Some(_) => Err(TypingError::OpaqueTypeConstrPattern {
                                            constr: id,
                                            span,
                                            module: self.module(),
                                        }),
                                        None => Ok((
                                            constrs.get(&name).unwrap(),
                                            id,
                                        )),
                                    }
                                }
                                _ => panic!(
                                    "tried to get a type constructor from a non-ADT type decl"
                                ),
                            }
                        }
                        // unit struct constructors
                        // NOTE: struct types are guaranteed to be non-opaque ADTs (see
                        // ast::unbound_lowered::SymType::is_struct)
                        Res::StructType(id) => {
                            let name = self.get_type(id).name;
                            let id = ast::TyConstrIndex { ty: id, name };

                            let named_ty = {
                                let nparams =
                                    self.get_type(id.ty).ast.params.len();
                                let name = id.ty;

                                let args = std::iter::repeat_with(|| {
                                    Arc::new(TyMatrix::Var(self.fresh_var()))
                                })
                                .take(nparams)
                                .collect();

                                self.instantiate(&Ty::unquantified(Arc::new(
                                    TyMatrix::Named { name, args },
                                )))
                            };

                            self.unify_matrices(named_ty, ty.matrix.clone())?;

                            let ty_decl = self.get_type(id.ty);
                            let constr = ty_decl
                                .ast
                                .constrs()
                                .and_then(|constrs| constrs.get(&name))
                                .unwrap();

                            Ok((constr, id))
                        }
                        // otherwise emit errors
                        Res::Term(id) => Err(TypingError::TermInNamePattern {
                            id,
                            span,
                            module: self.module(),
                        }),
                        Res::Type(id) => Err(TypingError::TypeInNamePattern {
                            id,
                            span,
                            module: self.module(),
                        }),
                        // we panic here, since something would have to have gone
                        // critically wrong in an earlier path
                        Res::Module(_) => {
                            panic!("module occurred as a pattern")
                        }
                    }?;

                    match &constr.kind {
                        ast::TyConstrKind::Unit(constr_ty) => {
                            // instantiate constructor
                            let constr_ty =
                                self.instantiate_uid(&constr_ty.clone());

                            // unify with expected type
                            self.unify_matrices(ty.matrix.clone(), constr_ty)?;

                            Ok(span.with(ast::Pattern::UnitConstr {
                                name: Name {
                                    content: bound.span().with(bound.clone()),
                                    id,
                                },
                            }))
                        }
                        _ => {
                            Err(TypingError::NonUnitConstrInUnitConstrPattern {
                                constr: id,
                                span,
                                module: self.module(),
                            })
                        }
                    }
                }
                // if the name is local, make a binding for the type
                Ok(Bound::Local(name @ Name { id, .. })) => {
                    if let Some(prev_ty) = self.local_var_types.get(id) {
                        self.unify(ty.clone(), prev_ty.clone())?;
                    } else {
                        self.local_var_types.insert(*id, ty.clone());
                    }

                    let ty = self.zonk(&ty);
                    Ok(span.with(ast::Pattern::Var(ty.with(*name))))
                }
                Err(_) => panic!("unbound AST name:\n{:?}", name),
            },
            bound::Pattern::Tuple(elems) => {
                let mut subpatterns = Vec::with_capacity(elems.len());
                let mut tys = Vec::with_capacity(elems.len());

                // for each subpattern
                for elem in elems {
                    // generate a fresh type variable and check against it
                    let elem_ty = Arc::new(TyMatrix::Var(self.fresh_var()));
                    let subpattern = self.check_pattern(
                        elem.as_ref(),
                        Arc::new(Ty {
                            prefix: ty.prefix.clone(),
                            matrix: elem_ty.clone(),
                        }),
                    )?;

                    tys.push(self.zonk_matrix(elem_ty));
                    subpatterns.push(subpattern);
                }

                let tys = tys.into_boxed_slice();
                let subpatterns = subpatterns.into_boxed_slice();

                // build a tuple from the subpattern types and unify
                let tuple_ty = Arc::new(TyMatrix::Tuple(tys));
                self.unify_matrices(ty.matrix.clone(), tuple_ty)?;
                Ok(span.with(ast::Pattern::Tuple(subpatterns)))
            }
            bound::Pattern::List(elems) => {
                // the T in List[T]
                let arg_ty = Arc::new(TyMatrix::Var(self.fresh_var()));
                let subpatterns = elems
                    .iter()
                    .try_fold(
                        Vec::with_capacity(elems.len()),
                        |mut pats, pat| {
                            let pat = self.check_pattern(
                                pat.as_ref(),
                                Arc::new(Ty {
                                    prefix: ty.prefix.clone(),
                                    matrix: arg_ty.clone(),
                                }),
                            )?;
                            pats.push(pat);
                            Ok(pats)
                        },
                    )?
                    .into_boxed_slice();

                // build a list type from the argument type and unify
                let list_ty = Arc::new(TyMatrix::Named {
                    name: self.list_id,
                    args: vec![arg_ty].into_boxed_slice(),
                });
                self.unify_matrices(ty.matrix.clone(), list_ty)?;
                Ok(span.with(ast::Pattern::List(subpatterns)))
            }
            bound::Pattern::Cons { head, tail } => {
                // the T in List[T]
                let arg_ty = Arc::new(TyMatrix::Var(self.fresh_var()));

                // first check against the head of the pattern, implicitly unifying the arg_ty
                let head = Box::new(self.check_pattern(
                    head.as_ref().as_ref(),
                    Arc::new(Ty {
                        prefix: ty.prefix.clone(),
                        matrix: arg_ty.clone(),
                    }),
                )?);

                let arg_ty = self.zonk_matrix(arg_ty);

                // then construct the corresponding list type
                let list_ty = Arc::new(TyMatrix::Named {
                    name: self.list_id,
                    args: vec![arg_ty.clone()].into_boxed_slice(),
                });

                // check the tail against this list type
                let tail = Box::new(self.check_pattern(
                    tail.as_ref().as_ref(),
                    Arc::new(Ty {
                        prefix: ty.prefix.clone(),
                        matrix: list_ty.clone(),
                    }),
                )?);

                // then unify against the expected type and return
                self.unify_matrices(ty.matrix.clone(), list_ty)?;
                Ok(span.with(ast::Pattern::Cons { head, tail }))
            }
            bound::Pattern::TupleConstr { name, elems } => {
                let bound = self.try_get_bound_ref(name)?;

                let constr_id = match bound.as_res() {
                    Some(Res::TyConstr { ty, name }) => {
                        Ok(ast::TyConstrIndex { ty, name })
                    }
                    _ => Err(TypingError::BadConstrInConstrPattern {
                        span,
                        module: self.module(),
                    }),
                }?;

                match self.lookup_constr(constr_id).kind.clone() {
                    ast::TyConstrKind::Tuple {
                        elems: elem_tys, ..
                    } => {
                        // instantiate ty params
                        let (args, elem_tys) = {
                            let ty_params = self.get_ty_params(constr_id.ty);

                            let (args, mut subst) = self
                                .make_param_instantiation(
                                    ty_params.iter().copied(),
                                );

                            let elem_tys = elem_tys
                                .iter()
                                .map(|ty| subst(ty.matrix.clone()))
                                .collect::<Box<[_]>>();

                            (args, elem_tys)
                        };

                        // check subpatterns
                        let elems = elems
                            .iter()
                            .map(Spanned::as_ref)
                            .zip(&elem_tys)
                            .try_fold(
                                Vec::new(),
                                |mut pats, (pat, elem_ty)| {
                                    let pat = self.check_pattern(
                                        pat,
                                        Arc::new(Ty {
                                            prefix: ty.prefix.clone(),
                                            matrix: elem_ty.clone(),
                                        }),
                                    )?;
                                    pats.push(pat);
                                    Ok(pats)
                                },
                            )?
                            .into_boxed_slice();

                        // construct the corresponding named type
                        let constr_ty = Arc::new(TyMatrix::Named {
                            name: constr_id.ty,
                            args,
                        });

                        // unify against expected type and return
                        self.unify_matrices(ty.matrix.clone(), constr_ty)?;
                        Ok(span.with(ast::Pattern::TupleConstr {
                            name: Name {
                                content: bound.span().with(bound.clone()),
                                id: constr_id,
                            },
                            elems,
                        }))
                    }
                    _ => Err(TypingError::BadConstrInConstrPattern {
                        span,
                        module: self.module(),
                    }),
                }
            }
            bound::Pattern::RecordConstr {
                name,
                fields: field_pats,
                rest,
            } => {
                let bound = self.try_get_bound_ref(name)?;

                let constr_id = match bound.as_res() {
                    Some(Res::TyConstr { ty, name }) => {
                        Ok(ast::TyConstrIndex { ty, name })
                    }
                    Some(Res::StructType(ty)) => {
                        let name = self.get_type(ty).name;
                        Ok(ast::TyConstrIndex { ty, name })
                    }
                    _ => Err(TypingError::BadConstrInConstrPattern {
                        span,
                        module: self.module(),
                    }),
                }?;

                match self.lookup_constr(constr_id).kind.clone() {
                    ast::TyConstrKind::Record(fields) => {
                        // throw an error if there are missing fields and
                        // the rest pattern syntax is not present
                        if rest.is_none() && field_pats.len() < fields.len() {
                            return Err(
                                TypingError::MissingRecordPatternFields {
                                    span,
                                    module: self.module(),
                                },
                            );
                        }

                        // instantiate ty params and field tys
                        let (args, field_tys) = {
                            let ty_params = self.get_ty_params(constr_id.ty);

                            let (args, mut subst) =
                                self.make_param_instantiation(ty_params);

                            let field_tys: HashMap<_, _> = fields
                                .into_iter()
                                .map(|(name, field)| {
                                    (name, subst(field.ty.matrix.clone()))
                                })
                                .collect();

                            (args, field_tys)
                        };

                        // check field patterns
                        let fields =
                            field_pats
                                .iter()
                                .map(Spanned::as_ref)
                                .try_fold(Vec::new(), |mut fields, field| {
                                    let span = field.span();
                                    let name = field.field.item;

                                    let ty = self.zonk(&Ty {
                                        prefix: ty.prefix.clone(),
                                        matrix: field_tys
                                            .get(&name)
                                            .unwrap()
                                            .clone(),
                                    });

                                    let pattern = self.check_pattern(
                                        field.pattern.as_ref(),
                                        ty,
                                    )?;

                                    fields.push(span.with(ast::FieldPattern {
                                        name,
                                        pattern,
                                    }));

                                    Ok(fields)
                                })?
                                .into_boxed_slice();

                        // construct the corresponding named type
                        let constr_ty = Arc::new(TyMatrix::Named {
                            name: constr_id.ty,
                            args,
                        });

                        // unify against expected type
                        self.unify_matrices(ty.matrix.clone(), constr_ty)?;
                        Ok(span.with(ast::Pattern::RecordConstr {
                            name: Name {
                                content: bound.span().with(bound.clone()),
                                id: constr_id,
                            },
                            fields,
                            rest: *rest,
                        }))
                    }
                    _ => Err(TypingError::BadConstrInConstrPattern {
                        span,
                        module: self.module(),
                    }),
                }
            }
        }
    }

    fn infer_literal(
        &mut self,
        Spanned { item, span }: Spanned<&bound::LiteralExpr>,
    ) -> Typed<Spanned<ast::LiteralExpr>, TyVar> {
        match *item {
            ast::LiteralExpr::Unit => {
                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Unit));
                ty.with(span.with(ast::LiteralExpr::Unit))
            }
            ast::LiteralExpr::Bool(value) => {
                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Bool));
                ty.with(span.with(ast::LiteralExpr::Bool(value)))
            }
            ast::LiteralExpr::Char(value) => {
                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Char));
                ty.with(span.with(ast::LiteralExpr::Char(value)))
            }
            ast::LiteralExpr::String(value) => {
                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::String));
                ty.with(span.with(ast::LiteralExpr::String(value)))
            }
            ast::LiteralExpr::Int(value) => {
                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Int));
                ty.with(span.with(ast::LiteralExpr::Int(value)))
            }
            ast::LiteralExpr::Float(value) => {
                let ty = Arc::new(ast::Ty::prim(ast::PrimTy::Float));
                ty.with(span.with(ast::LiteralExpr::Float(value)))
            }
            ast::LiteralExpr::Malformed(kind) => {
                let ty = Arc::new(ast::Ty::prim(match kind {
                    bound::MalformedLiteral::Char => ast::PrimTy::Char,
                    bound::MalformedLiteral::String => ast::PrimTy::String,
                    bound::MalformedLiteral::Int => ast::PrimTy::Int,
                }));

                ty.with(span.with(ast::LiteralExpr::Malformed(kind)))
            }
        }
    }

    fn reifier(&mut self) -> TyReifier<'_, TyVar> {
        // NOTE: we only call this method in the type_term path, where the
        // current_module is definitely Some(..).
        TyReifier::new(self.module(), None, self.errors)
    }

    fn try_get_bound_ref<'r>(
        &self,
        res: &'r BoundResult,
    ) -> Result<&'r Bound, TypingError> {
        res.as_ref().map_err(|content| TypingError::UnresolvedName {
            module: self.module(),
            name_content: content.clone(),
        })
    }

    fn get_type(&self, id: TypeId) -> Type<Spanned<&ast::Type<Uid>>> {
        self.types[id.0].as_ref().map(Spanned::as_ref)
    }

    fn generalize(&mut self, ty: Arc<Ty<TyVar>>) -> Arc<Ty<TyVar>> {
        // replace concrete variables with types
        let ty = self.zonk(&ty);

        // extract matrix and gather free variables
        let matrix = ty.matrix.clone();
        let prefix = matrix.vars();

        // return new generalized type
        Arc::new(Ty { prefix, matrix })
    }

    /// Recursively expands type aliases in the given `ty`, guaranteeing that
    /// the result is in a canonical form. Note that this includes normalization
    /// of functions with unit-equivalent domains to unary functions of the
    /// unit domain.
    ///
    /// We assume that `self.env` does not contain any recursive aliases, since
    /// otherwise this function cannot guarantee termination.
    fn normalize(
        &mut self,
        ty: &Arc<TyMatrix<TyVar>>,
    ) -> Option<Arc<TyMatrix<TyVar>>> {
        let ty = self.zonk_matrix(ty.clone());

        match ty.as_ref() {
            TyMatrix::Prim(_) | TyMatrix::Var(_) => Some(ty.clone()),
            TyMatrix::Tuple(elems) => Some(Arc::new(TyMatrix::Tuple(
                elems
                    .iter()
                    .try_fold(vec![], |mut elems, ty| {
                        let elem = self.normalize(ty)?;
                        elems.push(elem);
                        Some(elems)
                    })?
                    .into_boxed_slice(),
            ))),
            TyMatrix::Fn { domain, codomain } => Some(Arc::new(TyMatrix::Fn {
                domain: domain
                    .iter()
                    .try_fold(vec![], |mut elems, ty| {
                        let elem = self.normalize(ty)?;
                        elems.push(elem);
                        Some(elems)
                    })?
                    .into_boxed_slice(),
                codomain: self.normalize(codomain)?,
            })),
            TyMatrix::Named { name, args } => {
                let ast = self.get_type(*name).ast;
                let params = &ast.params;
                let kind = &ast.kind;

                Some(match kind {
                    // normalize the alias
                    ast::TypeKind::Alias { rhs_ty, .. } => {
                        // sanity check
                        assert_eq!(params.len(), args.len());

                        let substitution: HashMap<_, _> = params
                            .iter()
                            .zip(args)
                            .map(|(var, arg)| (var.id, arg.clone()))
                            .collect();

                        let rhs_matrix = rhs_ty.matrix.clone();
                        let mut rebinder =
                            |var: &Uid| self.get_or_assign_var(*var);
                        apply_substitution(
                            &substitution,
                            rhs_matrix,
                            &mut rebinder,
                        )
                    }
                    // otherwise recurse as normal
                    _ => Arc::new(TyMatrix::Named {
                        name: *name,
                        args: args
                            .iter()
                            .try_fold(vec![], |mut args, ty| {
                                let arg = self.normalize(ty)?;
                                args.push(arg);
                                Some(args)
                            })?
                            .into_boxed_slice(),
                    }),
                })
            }
        }
    }

    fn unify_var_value(
        &mut self,
        var: TyVar,
        value: Arc<TyMatrix<TyVar>>,
    ) -> UnitResult {
        let value = self.zonk_matrix(value);
        let value = self.normalize(&value).unwrap();

        if !occurs_check(&var, value.as_ref()) {
            self.assign_var(var, value);
            Ok(())
        } else {
            Err(TypingError::OccursIn(var, value))
        }
    }

    fn assign_var(&mut self, var: TyVar, ty: Arc<TyMatrix<TyVar>>) {
        // grab the representative element for `var`.
        let repr = self.unifier.find(var);

        // check for a preexisting assignment
        if let Some(current_ty) = self.lookup_var(repr) {
            // unify to check consistency with current_ty
            assert!(self.unify_matrices(current_ty, ty).is_ok());
        } else {
            // otherwise just create the new assignment
            let ty = self.zonk_matrix(ty);
            self.var_assignments.insert(repr, ty);
        }
    }

    fn instantiate(&mut self, ty: &Ty<TyVar>) -> Arc<TyMatrix<TyVar>> {
        let mut substitution = HashMap::with_capacity(ty.prefix.len());
        let ty = self.zonk(ty);

        for &var in &ty.prefix {
            substitution.insert(var, Arc::new(TyMatrix::Var(self.fresh_var())));
        }

        let mut rebinder = |var: &TyVar| *var;
        apply_substitution(&substitution, ty.matrix.clone(), &mut rebinder)
    }

    fn instantiate_uid(&mut self, ty: &Ty<Uid>) -> Arc<TyMatrix<TyVar>> {
        let mut substitution = HashMap::with_capacity(ty.prefix.len());

        for &var in &ty.prefix {
            substitution.insert(var, Arc::new(TyMatrix::Var(self.fresh_var())));
        }

        // NOTE: the rebinder is only invoked when a variable is not quantified
        let mut rebinder = |&var: &Uid| self.get_or_assign_var(var);
        apply_substitution(&substitution, ty.matrix.clone(), &mut rebinder)
    }

    /// Creates an instantiation for a sequence of `params`, returning:
    /// 1. a list of instantiated parameters, and;
    /// 2. a function that can instantiate matrices with the same substitution.
    ///
    /// Note that the function captures `&mut self`.
    #[allow(clippy::type_complexity, reason = "one-off return type")]
    fn make_param_instantiation(
        &mut self,
        params: impl IntoIterator<Item = Uid>,
    ) -> (
        Box<[Arc<TyMatrix<TyVar>>]>,
        impl FnMut(Arc<TyMatrix>) -> Arc<TyMatrix<TyVar>>,
    ) {
        let mut substitution = HashMap::new();
        let mut inst_params = Vec::new();

        for param in params.into_iter() {
            let var = Arc::new(TyMatrix::Var(self.fresh_var()));
            inst_params.push(var.clone());
            substitution.insert(param, var);
        }

        let mut rebinder = |&var: &Uid| self.get_or_assign_var(var);
        let func =
            move |ty| apply_substitution(&substitution, ty, &mut rebinder);
        (inst_params.into_boxed_slice(), func)
    }

    /// A helper method for zonking the type of a `Spanned<Typed<T, TyVar>>`.
    fn zonk_spty<T>(
        &mut self,
        Spanned { item, span }: Spanned<Typed<T, TyVar>>,
    ) -> Spanned<Typed<T, TyVar>> {
        let item = item.map_ty(|ty| self.zonk(&ty));
        span.with(item)
    }

    fn zonk(&mut self, ty: &Ty<TyVar>) -> Arc<Ty<TyVar>> {
        let matrix = self.zonk_matrix(ty.matrix.clone());

        // remove phantom prefix variables
        let vars = matrix.vars();
        let prefix = ty
            .prefix
            .iter()
            .copied()
            .filter(|var| vars.contains(var))
            .collect();

        Arc::new(Ty { prefix, matrix })
    }

    fn zonk_matrix(
        &mut self,
        matrix: Arc<TyMatrix<TyVar>>,
    ) -> Arc<TyMatrix<TyVar>> {
        match matrix.as_ref() {
            TyMatrix::Prim(_) => matrix,
            TyMatrix::Var(var) => {
                let repr = self.unifier.find(*var);
                self.lookup_var(repr)
                    .map(|ty| self.zonk_matrix(ty))
                    .unwrap_or_else(|| Arc::new(TyMatrix::Var(repr)))
            }
            TyMatrix::Tuple(tys) => Arc::new(TyMatrix::Tuple(
                tys.iter().cloned().map(|ty| self.zonk_matrix(ty)).collect(),
            )),
            TyMatrix::Named { name, args } => Arc::new(TyMatrix::Named {
                name: *name,
                args: args
                    .iter()
                    .cloned()
                    .map(|arg| self.zonk_matrix(arg))
                    .collect(),
            }),
            TyMatrix::Fn { domain, codomain } => Arc::new(TyMatrix::Fn {
                domain: domain
                    .iter()
                    .cloned()
                    .map(|ty| self.zonk_matrix(ty))
                    .collect(),
                codomain: self.zonk_matrix(codomain.clone()),
            }),
        }
    }

    fn lookup_constr(
        &self,
        ast::TyConstrIndex { ty, name }: ast::TyConstrIndex,
    ) -> Spanned<&ast::TyConstr<Uid>> {
        match self.get_type(ty).ast.constrs() {
            Some(constrs) => match constrs.get(&name) {
                Some(constr) => constr.as_ref(),
                None => {
                    panic!("invalid TyConstrIndex: name is not a constructor")
                }
            },
            None => panic!("invalid TyConstrIndex: ty is not an ADT"),
        }
    }

    fn get_ty_params(&self, id: TypeId) -> Box<[Uid]> {
        self.get_type(id)
            .ast
            .params
            .iter()
            .map(|name| name.id)
            .collect()
    }

    fn lookup_var(&mut self, var: TyVar) -> Option<Arc<TyMatrix<TyVar>>> {
        let repr = self.unifier.find(var);
        self.var_assignments.get(&repr).cloned()
    }

    fn fresh_var(&mut self) -> TyVar {
        self.unifier.new_key(())
    }

    /// Returns the current module.
    fn module(&self) -> ModId {
        self.current_module
    }

    /// Checks every public term in `env` to see if its annotation is
    /// concrete, emitting errors if this is not the case.
    fn check_public_term_annotations(&mut self, env: &ResEnv) {
        for id in env.term_id_iter() {
            let Term { name, module, .. } = env.get_term(id);
            let is_public = env
                .get_module(*module)
                .items
                .get(name)
                .map(Vis::is_visible)
                .unwrap_or(false);

            if is_public && !self.term_types.get(&id).unwrap().is_concrete() {
                let error = TypingError::PubTermTyIsNotConcrete { id };
                self.errors.push(error);
            }
        }
    }

    // UID CONVERSION METHODS

    /// Returns the assigned [`TyVar`] for the given [`Uid`], making a new
    /// assignment if necessary.
    fn get_or_assign_var(&mut self, uid: Uid) -> TyVar {
        match self.uid_assigments.get(&uid) {
            Some(&var) => var,
            None => {
                let var = self.fresh_var();
                self.uid_assigments.insert(uid, var);
                var
            }
        }
    }

    fn rebind_with(
        &mut self,
        ty: Ty<Uid>,
        substitution: &HashMap<Uid, Arc<TyMatrix<TyVar>>>,
    ) -> Arc<Ty<TyVar>> {
        let prefix = ty
            .prefix
            .into_iter()
            .filter_map(|var| match substitution.contains_key(&var) {
                true => Some(self.get_or_assign_var(var)),
                false => None,
            })
            .collect();

        let mut rebinder = |&var: &Uid| self.get_or_assign_var(var);
        let matrix = apply_substitution(substitution, ty.matrix, &mut rebinder);

        Arc::new(Ty { prefix, matrix })
    }

    /// Converts a [`Ty<N, Uid>`] into a [`Ty<N, TyVar>`].
    fn rebind(&mut self, ty: &Ty<Uid>) -> Arc<Ty<TyVar>> {
        let matrix = self.rebind_matrix(&ty.matrix);
        let prefix = ty
            .prefix
            .iter()
            .map(|&uid| self.get_or_assign_var(uid))
            .collect();

        Arc::new(Ty { prefix, matrix })
    }

    /// Converts a [`TyMatrix<N, Uid>`] into a [`TyMatrix<N, TyVar>`].
    fn rebind_matrix(&mut self, ty: &TyMatrix<Uid>) -> Arc<TyMatrix<TyVar>> {
        Arc::new(match ty {
            TyMatrix::Prim(prim_ty) => TyMatrix::Prim(*prim_ty),
            TyMatrix::Var(uid) => TyMatrix::Var(self.get_or_assign_var(*uid)),
            TyMatrix::Tuple(elems) => TyMatrix::Tuple(
                elems.iter().map(|ty| self.rebind_matrix(ty)).collect(),
            ),
            TyMatrix::Named { name, args } => TyMatrix::Named {
                name: *name,
                args: args.iter().map(|ty| self.rebind_matrix(ty)).collect(),
            },
            TyMatrix::Fn { domain, codomain } => TyMatrix::Fn {
                domain: domain
                    .iter()
                    .map(|ty| self.rebind_matrix(ty))
                    .collect(),
                codomain: self.rebind_matrix(codomain),
            },
        })
    }
}

/// Returns `true` if and only if `var` occurs in `ty`.
fn occurs_check<V: Eq>(var: &V, ty: &TyMatrix<V>) -> bool {
    match ty {
        TyMatrix::Prim(_) => false,
        TyMatrix::Var(v) => v == var,
        TyMatrix::Tuple(elems) => elems.iter().any(|ty| occurs_check(var, ty)),
        TyMatrix::Named { name: _, args } => {
            args.iter().any(|ty| occurs_check(var, ty))
        }
        TyMatrix::Fn { domain, codomain } => {
            domain.iter().any(|ty| occurs_check(var, ty))
                || occurs_check(var, codomain)
        }
    }
}

fn apply_substitution<F, V1, V2>(
    substitution: &HashMap<V1, Arc<TyMatrix<V2>>>,
    ty: Arc<TyMatrix<V1>>,
    rebinder: &mut F,
) -> Arc<TyMatrix<V2>>
where
    V1: Hash + Eq,
    F: FnMut(&V1) -> V2,
{
    match ty.as_ref() {
        TyMatrix::Prim(prim_ty) => Arc::new(TyMatrix::Prim(*prim_ty)),
        TyMatrix::Var(var) => substitution
            .get(var)
            .cloned()
            .unwrap_or_else(|| Arc::new(TyMatrix::Var(rebinder(var)))),
        TyMatrix::Tuple(elems) => Arc::new(ast::TyMatrix::Tuple(
            elems
                .iter()
                .cloned()
                .map(|ty| apply_substitution(substitution, ty, rebinder))
                .collect(),
        )),
        TyMatrix::Named { name, args } => Arc::new(ast::TyMatrix::Named {
            name: *name,
            args: args
                .iter()
                .cloned()
                .map(|ty| apply_substitution(substitution, ty, rebinder))
                .collect(),
        }),
        TyMatrix::Fn { domain, codomain } => Arc::new(ast::TyMatrix::Fn {
            domain: domain
                .iter()
                .cloned()
                .map(|ty| apply_substitution(substitution, ty, rebinder))
                .collect(),
            codomain: apply_substitution(
                substitution,
                codomain.clone(),
                rebinder,
            ),
        }),
    }
}

/// Given a list of type matrices, determines whether it can be treated as
/// equivalent to the unit type in the domain of a function type. This is
/// the case if and only if either
/// 1. the domain has no members, or;
/// 2. the domain has exactly one member, and this member is `()`.
fn is_unit_domain<V>(domain: &[Arc<TyMatrix<V>>]) -> bool {
    match domain {
        [] => true,
        [_, _, ..] => false,
        [ty] => matches!(ty.as_ref(), TyMatrix::Prim(ast::PrimTy::Unit)),
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        cst::Parser,
        env::{
            import_res::ImportResEnv, resolve::resolve, typed::TypingError,
            unbound::UnboundEnv,
        },
        package as pkg,
    };
    use std::{path::PathBuf, str::FromStr};

    #[test]
    fn build_lowered_env_from_core() {
        // load package CSTs
        let path = PathBuf::from_str("../libs/core").unwrap();
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
        let mut env = match super::typecheck(env) {
            Ok(env) => env,
            Err((env, errors)) => {
                for error in errors {
                    match error {
                        TypingError::CalleeTyIsNotFn {
                            callee_ty,
                            span,
                            module,
                        } => {
                            let module = env.get_module(module);
                            let file = env.get_file(module.file);

                            let spanned_content = span
                                .in_source(file.contents().as_bytes())
                                .unwrap();
                            let module_name =
                                env.interner.resolve(module.name).unwrap();

                            eprintln!(
                                "in module {module_name}, callee type {callee_ty:?} is not a function:\n{spanned_content}"
                            );
                        }
                        TypingError::MutateLhsIsNotStruct {
                            lhs_span,
                            span,
                            module,
                        } => {
                            let module = env.get_module(module);
                            let file = env.get_file(module.file);

                            let expr = span
                                .in_source(file.contents().as_bytes())
                                .unwrap();

                            let lhs = lhs_span
                                .in_source(file.contents().as_bytes())
                                .unwrap();
                            let module_name =
                                env.interner.resolve(module.name).unwrap();

                            eprintln!(
                                "in module {module_name}\nin expression {expr}\nthe expression {lhs} is not a struct"
                            );
                        }
                        error => {
                            dbg![error];
                        }
                    }
                }

                panic!()
            }
        };

        // __TEST MODULE INSPECTION

        let __test = env.interner.intern_static("__test");
        let test_mod_id = env.magic_core_submodule(__test).unwrap();
        let test_mod = env.get_module(test_mod_id);

        for (sym, item) in test_mod.items.clone() {
            let name = env.interner.resolve(sym).unwrap();
            let (_vis, _span, res) = item.spread();

            let res_value = env.get_res(res);

            eprintln!("{} ({:?})\n{:?}\n\n", name, res, res_value);
        }

        panic!();
    }
}
