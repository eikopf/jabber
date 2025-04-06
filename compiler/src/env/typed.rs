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

use std::{collections::HashMap, fmt::Debug, hash::Hash, sync::Arc};

use ena::unify::{InPlace, UnificationTable, UnifyKey};
use lower::TyReifier;

use crate::{
    ast::{
        bound::{self, Bound, Name},
        common::{NameEquiv, ViSp, Vis},
        typed::{self as ast, Ty, TyMatrix, Typed},
    },
    env::{Env, Res, resolve::BoundResult},
    span::{Span, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

use super::{ModId, Term, TermId, TryGetRes, Type, TypeId, resolve::ResEnv};

pub mod lower;

/// A typechecked [`Env`].
pub type TypedEnv<N = BoundResult> = Env<
    Spanned<ast::Term<N, TyVar>>,
    Spanned<ast::Type<N, Uid>>,
    HashMap<Symbol, ViSp<Res>>,
>;

#[derive(Debug, Clone)]
pub enum TypingError<N, V = TyVar> {
    Lower(lower::TyLowerError),
    DidNotUnify(Arc<TyMatrix<N, V>>, Arc<TyMatrix<N, V>>),
    OccursIn(V, Arc<TyMatrix<N, V>>),
    UnboundName(N),
    ExternFnTyIsNotConcrete {
        id: TermId,
        ty: Arc<Ty<N, V>>,
    },
    PubTermTyIsNotConcrete {
        id: TermId,
    },
    NonConcreteAliasRhs {
        id: TypeId,
    },
    RecursiveAliasRhs {
        id: TypeId,
        occurrence: N,
    },
    PhantomTypeParameter {
        id: TypeId,
        param: N,
    },
    UsedTyParamAsPolytype {
        param: N,
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
    OpaqueTypeConstrPattern {
        constr: ast::TyConstrIndex,
        span: Span,
        module: ModId,
    },
}

// TODO: we have roughly three tasks here:
// 1. rescue the `lower` implementation to implement the first pass
// 2. write the second pass in this module
// 3. refactor to remove old dead code and redundant boilerplate
// when this is complete, you MUST write at least one test

pub fn typecheck(
    env: ResEnv,
) -> Result<TypedEnv<BoundResult>, (ResEnv, Vec<TypingError<BoundResult>>)> {
    // first pass
    let (types, term_types, mut errors) = lower::collect_types(&env);

    let mut typer = Typer::new(&types, &term_types, &mut errors);
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

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct TyVar(u32);

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

/// An index into a [`Typer`].
#[derive(Debug, Clone, Copy)]
pub enum TyperIndex {
    Res(Res),
    Uid(Uid),
}

pub trait TryGetTyperIndex {
    type Error;

    fn try_get_typer_index(&self) -> Result<TyperIndex, Self::Error>;
}

impl TryGetTyperIndex for Res {
    type Error = std::convert::Infallible;

    fn try_get_typer_index(&self) -> Result<TyperIndex, Self::Error> {
        Ok(TyperIndex::Res(*self))
    }
}

impl TryGetTyperIndex for Uid {
    type Error = std::convert::Infallible;

    fn try_get_typer_index(&self) -> Result<TyperIndex, Self::Error> {
        Ok(TyperIndex::Uid(*self))
    }
}

impl<I: TryGetTyperIndex, C> TryGetTyperIndex for Name<I, C> {
    type Error = I::Error;

    fn try_get_typer_index(&self) -> Result<TyperIndex, Self::Error> {
        self.id.try_get_typer_index()
    }
}

impl TryGetTyperIndex for Bound {
    type Error = std::convert::Infallible;

    fn try_get_typer_index(&self) -> Result<TyperIndex, Self::Error> {
        match self {
            Bound::Local(name) => name.try_get_typer_index(),
            Bound::Path(name) => name.try_get_typer_index(),
            Bound::Global(name) => name.try_get_typer_index(),
        }
    }
}

impl<T: TryGetTyperIndex, E> TryGetTyperIndex for Result<T, E> {
    type Error = Option<T::Error>;

    fn try_get_typer_index(&self) -> Result<TyperIndex, Self::Error> {
        match self {
            Ok(inner) => inner.try_get_typer_index().map_err(Some),
            Err(_) => Err(None),
        }
    }
}

type TyExprResult<N, V = TyVar> =
    Result<Spanned<Typed<ast::Expr<N, V>, N, V>>, TypingError<N, V>>;

type InferResult<N, V = TyVar> = Result<
    (Spanned<Typed<ast::Expr<N, V>, N, V>>, Arc<Ty<N, V>>),
    TypingError<N, V>,
>;

type TyResult<N, V = TyVar> = Result<Arc<Ty<N, V>>, TypingError<N, V>>;
type UnitResult<N, V = TyVar> = Result<(), TypingError<N, V>>;

pub struct Typer<'a> {
    /// The lowered type declarations.
    types: &'a [lower::LoweredType<BoundResult, Uid>],
    /// A map from terms to their types.
    term_types: &'a lower::TermTypeMap<BoundResult, Uid>,
    /// Accumulated errors.
    errors: &'a mut Vec<TypingError<BoundResult>>,
    /// Equivalence classes of [`TyVar`].
    unifier: UnificationTable<InPlace<TyVar>>,
    /// A mapping from type variables to types.
    var_assignments: HashMap<TyVar, Arc<TyMatrix<BoundResult, TyVar>>>,
    /// A mapping from [`Uid`] to [`TyVar`] in type expressions.
    uid_assigments: HashMap<Uid, TyVar>,
    /// The type judgements associated with local variables.
    local_var_types: HashMap<Uid, Arc<Ty<BoundResult, TyVar>>>,
    /// The current module, if any.
    current_module: Option<ModId>,
}

impl<'a> Typer<'a> {
    pub fn new(
        types: &'a [lower::LoweredType<BoundResult>],
        term_types: &'a lower::TermTypeMap<BoundResult>,
        errors: &'a mut Vec<TypingError<BoundResult>>,
    ) -> Self {
        Self {
            types,
            term_types,
            errors,
            unifier: Default::default(),
            var_assignments: Default::default(),
            uid_assigments: Default::default(),
            local_var_types: Default::default(),
            current_module: None,
        }
    }

    /// Types the given term, returning `Some(..)` if and only if no errors
    /// occurred while typechecking.
    pub fn type_term(
        &mut self,
        id: TermId,
        Term { name, module, ast }: Term<Spanned<&bound::Term<BoundResult>>>,
    ) -> Result<
        Term<Spanned<ast::Term<BoundResult, TyVar>>>,
        TypingError<BoundResult>,
    > {
        // set current module
        self.current_module = Some(module);

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
                let params = self.lower_params(params)?;
                let (body, ty) = self.infer(body.as_ref().as_ref())?;
                self.unify(ty.clone(), annotated_ty)?;

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
                let (value, ty) = self.infer(value.as_ref())?;
                self.unify(ty.clone(), annotated_ty)?;

                ast::Term {
                    attrs: attrs.clone(),
                    name: *name,
                    ty,
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
    ) -> TyExprResult<BoundResult> {
        let (typed_expr, _ty) = self.infer(expr)?;
        Ok(typed_expr)
    }

    pub fn check(
        &mut self,
        expr: &ast::Expr<BoundResult>,
        ty: Arc<Ty<BoundResult, TyVar>>,
    ) -> TyResult<BoundResult> {
        todo!()
    }

    pub fn infer(
        &mut self,
        Spanned { item, span }: Spanned<&bound::Expr<BoundResult>>,
    ) -> InferResult<BoundResult> {
        match item {
            bound::Expr::Name(name) => {
                let ty = name
                    .try_get_typer_index()
                    .ok()
                    .and_then(|index| self.lookup_index(index));

                match ty {
                    Some(ty) => {
                        let expr = ast::Expr::Name(name.clone());
                        Ok((span.with(ty.with(expr)), ty))
                    }
                    None => Err(TypingError::UnboundName(name.clone())),
                }
            }
            bound::Expr::Literal(literal_expr) => todo!(),
            bound::Expr::List(_) => todo!(),
            bound::Expr::Tuple(_) => todo!(),
            bound::Expr::Block(block) => todo!(),
            bound::Expr::RecordConstr { name, fields, base } => todo!(),
            bound::Expr::RecordField { item, field } => todo!(),
            bound::Expr::TupleField { item, field } => todo!(),
            bound::Expr::Lambda { params, body } => todo!(),
            bound::Expr::Call { callee, args, kind } => todo!(),
            bound::Expr::LazyAnd { operator, lhs, rhs } => todo!(),
            bound::Expr::LazyOr { operator, lhs, rhs } => todo!(),
            bound::Expr::Mutate { operator, lhs, rhs } => todo!(),
            bound::Expr::Match { scrutinee, arms } => todo!(),
            bound::Expr::IfElse {
                condition,
                consequence,
                alternative,
            } => todo!(),
        }
    }

    pub fn unify(
        &mut self,
        t1: Arc<Ty<BoundResult, TyVar>>,
        t2: Arc<Ty<BoundResult, TyVar>>,
    ) -> UnitResult<BoundResult> {
        self.unify_matrices(t1.matrix.clone(), t2.matrix.clone())
    }

    fn unify_matrices(
        &mut self,
        t1: Arc<TyMatrix<BoundResult, TyVar>>,
        t2: Arc<TyMatrix<BoundResult, TyVar>>,
    ) -> UnitResult<BoundResult> {
        match (t1.as_ref(), t2.as_ref()) {
            // identical primitives
            (TyMatrix::Prim(p1), TyMatrix::Prim(p2)) if p1 == p2 => Ok(()),

            // variable-variable
            (TyMatrix::Var(v1), TyMatrix::Var(v2)) => {
                self.unifier.union(*v1, *v2);
                Ok(())
            }

            // value-variable & variable-value
            (_, TyMatrix::Var(var)) => self.unify_var_value(*var, t1),
            (TyMatrix::Var(var), _) => self.unify_var_value(*var, t2),

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
                // we have to check for equivalence of n1 and n2, but precisely
                // what _equivalence_ means here should depend on N; hence we
                // use the NameEquiv trait to check for equivalence. if they
                // are equivalent then we unify a1 and a2 pointwise

                if n1.equiv(n2) && a1.len() == a2.len() {
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

    fn lookup_index(
        &mut self,
        index: TyperIndex,
    ) -> Option<Arc<Ty<BoundResult, TyVar>>> {
        match index {
            TyperIndex::Uid(uid) => self.local_var_types.get(&uid).cloned(),
            TyperIndex::Res(Res::Term(id)) => {
                self.term_types.get(&id).map(|ty| self.rebind(ty))
            }
            TyperIndex::Res(Res::TyConstr { ty, name }) => self.types[ty.0]
                .ast
                .constrs()
                .and_then(|constrs| constrs.get(&name))
                .and_then(|constr| constr.get_ty())
                .map(|ty| self.rebind(ty.as_ref())),
            TyperIndex::Res(_) => {
                panic!("a variable was bound to a module or type")
            }
        }
    }

    fn lower_params(
        &mut self,
        params: &[Spanned<bound::Parameter<BoundResult>>],
    ) -> Result<
        SpanSeq<ast::Parameter<BoundResult, TyVar>>,
        TypingError<BoundResult>,
    > {
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
                let ty = reifier.quantify(matrix);

                self.rebind(&ty)
            };

            let pattern = self.check_pattern(pattern.as_ref(), ty.clone())?;

            let pat = ast::Parameter {
                pattern,
                ty,
                ty_ast: ty_ast.clone(),
            };

            typed_params.push(span.with(pat));
        }

        Ok(typed_params.into_boxed_slice())
    }

    fn check_pattern(
        &mut self,
        Spanned { item, span }: Spanned<&bound::Pattern<BoundResult>>,
        ty: Arc<Ty<BoundResult, TyVar>>,
    ) -> Result<Spanned<ast::Pattern>, TypingError<BoundResult>> {
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
                            let ast = &self.get_type(id).ast;
                            let id = ast::TyConstrIndex { ty: id, name };

                            match &ast.kind {
                                ast::TypeKind::Adt { opacity, constrs } => {
                                    match opacity {
                                        Some(_) => Err(TypingError::OpaqueTypeConstrPattern {
                                            constr: id,
                                            span,
                                            module: self.current_module.unwrap(),
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
                            let ty_decl = self.get_type(id);
                            let name = ty_decl.name;
                            let constr = ty_decl
                                .ast
                                .constrs()
                                .and_then(|constrs| constrs.get(&name))
                                .unwrap();

                            let id = ast::TyConstrIndex { ty: id, name };

                            Ok((constr, id))
                        }
                        // otherwise emit errors
                        Res::Term(id) => Err(TypingError::TermInNamePattern {
                            id,
                            span,
                            module: self.current_module.unwrap(),
                        }),
                        Res::Type(id) => Err(TypingError::TypeInNamePattern {
                            id,
                            span,
                            module: self.current_module.unwrap(),
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
                                module: self.current_module.unwrap(),
                            })
                        }
                    }
                }
                // if the name is local, make a binding for the type
                Ok(Bound::Local(name @ Name { id, .. })) => {
                    if !self.local_var_types.contains_key(id) {
                        self.local_var_types.insert(*id, ty);
                    }

                    Ok(span.with(ast::Pattern::Name(*name)))
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
                        Ty::unquantified(elem_ty.clone()),
                    )?;

                    tys.push(elem_ty);
                    subpatterns.push(subpattern);
                }

                let tys = tys.into_boxed_slice();
                let subpatterns = subpatterns.into_boxed_slice();

                // build a tuple from the subpattern types and unify
                let tuple_ty = Arc::new(TyMatrix::Tuple(tys));
                self.unify_matrices(ty.matrix.clone(), tuple_ty)?;
                Ok(span.with(ast::Pattern::Tuple(subpatterns)))
            }
            bound::Pattern::List(elems) => todo!(),
            bound::Pattern::Cons { head, tail } => todo!(),
            bound::Pattern::TupleConstr { name, elems } => todo!(),
            bound::Pattern::RecordConstr { name, fields, rest } => todo!(),
        }
    }

    fn infer_literal(
        &mut self,
        Spanned { item, span }: Spanned<&bound::LiteralExpr>,
    ) -> Typed<Spanned<ast::LiteralExpr>, BoundResult, TyVar> {
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

    fn reifier(&mut self) -> TyReifier<'_, BoundResult, TyVar>
    where
        BoundResult: Eq + Hash + Clone + TryGetTyperIndex,
    {
        // NOTE: we only call this method in the type_term path, where the
        // current_module is definitely Some(..).
        TyReifier::new(self.current_module.unwrap(), None, self.errors)
    }

    fn get_type(
        &self,
        id: TypeId,
    ) -> Type<Spanned<&ast::Type<BoundResult, Uid>>> {
        self.types[id.0].as_ref().map(Spanned::as_ref)
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
        ty: &Arc<TyMatrix<BoundResult, TyVar>>,
    ) -> Option<Arc<TyMatrix<BoundResult, TyVar>>>
    where
        BoundResult: TryGetRes + Clone,
    {
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
                let res: Res = name.try_get_res().ok()?;
                let ast = &self.types[res.as_type()?.0].ast;
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
                        name: name.clone(),
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
        value: Arc<TyMatrix<BoundResult, TyVar>>,
    ) -> UnitResult<BoundResult> {
        if !occurs_check(&var, value.as_ref()) {
            self.assign_var(var, value);
            Ok(())
        } else {
            Err(TypingError::OccursIn(var, value))
        }
    }

    fn assign_var(
        &mut self,
        var: TyVar,
        ty: Arc<TyMatrix<BoundResult, TyVar>>,
    ) {
        // grab the representative element for `var`.
        let repr = self.unifier.find(var);

        // check for a preexisting assignment
        if let Some(current_ty) = self.lookup_var(repr) {
            // unify to check consistency with current_ty
            assert!(self.unify_matrices(current_ty, ty).is_ok());
        } else {
            // otherwise just create the new assignment
            self.var_assignments.insert(repr, ty);
        }
    }

    fn instantiate(
        &mut self,
        ty: &Ty<BoundResult, TyVar>,
    ) -> Arc<TyMatrix<BoundResult, TyVar>> {
        let mut substitution = HashMap::with_capacity(ty.prefix.len());

        for &var in &ty.prefix {
            substitution.insert(var, Arc::new(TyMatrix::Var(self.fresh_var())));
        }

        let mut rebinder = |var: &TyVar| *var;
        apply_substitution(&substitution, ty.matrix.clone(), &mut rebinder)
    }

    fn instantiate_uid(
        &mut self,
        ty: &Ty<BoundResult, Uid>,
    ) -> Arc<TyMatrix<BoundResult, TyVar>> {
        let mut substitution = HashMap::with_capacity(ty.prefix.len());

        for &var in &ty.prefix {
            substitution.insert(var, Arc::new(TyMatrix::Var(self.fresh_var())));
        }

        let mut rebinder = |&var: &Uid| self.get_or_assign_var(var);
        apply_substitution(&substitution, ty.matrix.clone(), &mut rebinder)
    }

    fn zonk(
        &mut self,
        ty: &Ty<BoundResult, TyVar>,
    ) -> Arc<Ty<BoundResult, TyVar>> {
        let matrix = self.zonk_matrix(ty.matrix.clone());
        Arc::new(Ty {
            prefix: ty.prefix.clone(),
            matrix,
        })
    }

    fn zonk_matrix(
        &mut self,
        matrix: Arc<TyMatrix<BoundResult, TyVar>>,
    ) -> Arc<TyMatrix<BoundResult, TyVar>> {
        match matrix.as_ref() {
            TyMatrix::Prim(_) => matrix,
            TyMatrix::Var(var) => {
                self.var_assignments.get(var).cloned().unwrap_or(matrix)
            }
            TyMatrix::Tuple(tys) => Arc::new(TyMatrix::Tuple(
                tys.iter().cloned().map(|ty| self.zonk_matrix(ty)).collect(),
            )),
            TyMatrix::Named { name, args } => Arc::new(TyMatrix::Named {
                name: name.clone(),
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

    fn lookup_var(
        &mut self,
        var: TyVar,
    ) -> Option<Arc<TyMatrix<BoundResult, TyVar>>> {
        let repr = self.unifier.find(var);
        self.var_assignments.get(&repr).cloned()
    }

    fn fresh_var(&mut self) -> TyVar {
        self.unifier.new_key(())
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

    /// Converts a [`Ty<N, Uid>`] into a [`Ty<N, TyVar>`].
    fn rebind(
        &mut self,
        ty: &Ty<BoundResult, Uid>,
    ) -> Arc<Ty<BoundResult, TyVar>> {
        let matrix = self.rebind_matrix(&ty.matrix);
        let prefix = ty
            .prefix
            .iter()
            .map(|&uid| self.get_or_assign_var(uid))
            .collect();

        Arc::new(Ty { prefix, matrix })
    }

    /// Converts a [`TyMatrix<N, Uid>`] into a [`TyMatrix<N, TyVar>`].
    fn rebind_matrix(
        &mut self,
        ty: &TyMatrix<BoundResult, Uid>,
    ) -> Arc<TyMatrix<BoundResult, TyVar>> {
        Arc::new(match ty {
            TyMatrix::Prim(prim_ty) => TyMatrix::Prim(*prim_ty),
            TyMatrix::Var(uid) => TyMatrix::Var(self.get_or_assign_var(*uid)),
            TyMatrix::Tuple(elems) => TyMatrix::Tuple(
                elems.iter().map(|ty| self.rebind_matrix(ty)).collect(),
            ),
            TyMatrix::Named { name, args } => TyMatrix::Named {
                name: name.clone(),
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
fn occurs_check<N, V: Eq>(var: &V, ty: &TyMatrix<N, V>) -> bool {
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

fn apply_substitution<N, F, V1, V2>(
    substitution: &HashMap<V1, Arc<TyMatrix<N, V2>>>,
    ty: Arc<TyMatrix<N, V1>>,
    rebinder: &mut F,
) -> Arc<TyMatrix<N, V2>>
where
    N: Clone,
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
            name: name.clone(),
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
fn is_unit_domain<N, V>(domain: &[Arc<TyMatrix<N, V>>]) -> bool {
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
            import_res::ImportResEnv, resolve::resolve, unbound::UnboundEnv,
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
        let mut env = super::typecheck(env).unwrap();

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

        panic!();
    }
}
