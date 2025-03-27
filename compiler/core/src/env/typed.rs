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

use crate::{
    ast::{
        bound::{self, Bound, Name},
        common::{NameEquiv, ViSp, Vis},
        typed::{self as ast, Ty, TyMatrix, Typed},
    },
    env::{Env, Res, resolve::BoundResult},
    span::{SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

use super::{Term, TermId, TryGetRes, resolve::ResEnv};

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
    ExternFnTyIsNotConcrete { id: TermId, ty: Arc<Ty<N, V>> },
    PubTermTyIsNotConcrete { id: TermId },
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
    let (types, term_types, errors) = lower::collect_types(&env);

    let mut errors = errors.into_iter().map(TypingError::Lower).collect();
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

pub struct Typer<'a, N> {
    /// The lowered type declarations.
    types: &'a [lower::LoweredType<N, Uid>],
    /// A map from terms to their types.
    term_types: &'a lower::TermTypeMap<N, Uid>,
    /// Accumulated errors.
    errors: &'a mut Vec<TypingError<N>>,
    /// Equivalence classes of [`TyVar`].
    unifier: UnificationTable<InPlace<TyVar>>,
    /// A mapping from type variables to types.
    var_assignments: HashMap<TyVar, Arc<TyMatrix<N, TyVar>>>,
    /// A mapping from [`Uid`] to [`TyVar`] in type expressions.
    uid_assigments: HashMap<Uid, TyVar>,
    /// The type judgements associated with local variables.
    local_var_types: HashMap<Uid, Arc<Ty<N, TyVar>>>,
}

impl<'a, N> Typer<'a, N> {
    pub fn new(
        types: &'a [lower::LoweredType<N>],
        term_types: &'a lower::TermTypeMap<N>,
        errors: &'a mut Vec<TypingError<N>>,
    ) -> Self {
        Self {
            types,
            term_types,
            errors,
            unifier: Default::default(),
            var_assignments: Default::default(),
            uid_assigments: Default::default(),
            local_var_types: Default::default(),
        }
    }

    /// Types the given term, returning `Some(..)` if and only if no errors
    /// occurred while typechecking.
    pub fn type_term(
        &mut self,
        id: TermId,
        Term { name, module, ast }: Term<Spanned<&bound::Term<N>>>,
    ) -> Result<Term<Spanned<ast::Term<N, TyVar>>>, TypingError<N>>
    where
        N: TryGetTyperIndex + NameEquiv + Clone,
    {
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
                let params = self.lower_params(params);
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
                let params = self.lower_params(params);
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
        expr: Spanned<&bound::Expr<N>>,
    ) -> TyExprResult<N>
    where
        N: TryGetTyperIndex + Clone,
    {
        let (typed_expr, _ty) = self.infer(expr)?;
        Ok(typed_expr)
    }

    pub fn check(
        &mut self,
        expr: &ast::Expr<N>,
        ty: Arc<Ty<N, TyVar>>,
    ) -> TyResult<N> {
        todo!()
    }

    pub fn infer(
        &mut self,
        Spanned { item, span }: Spanned<&bound::Expr<N>>,
    ) -> InferResult<N>
    where
        N: TryGetTyperIndex + Clone,
    {
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
        t1: Arc<Ty<N, TyVar>>,
        t2: Arc<Ty<N, TyVar>>,
    ) -> UnitResult<N>
    where
        N: NameEquiv,
    {
        self.unify_matrices(t1.matrix.clone(), t2.matrix.clone())
    }

    fn unify_matrices(
        &mut self,
        t1: Arc<TyMatrix<N, TyVar>>,
        t2: Arc<TyMatrix<N, TyVar>>,
    ) -> UnitResult<N>
    where
        N: NameEquiv,
    {
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

                if N::equiv(n1, n2) && a1.len() == a2.len() {
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

    fn lookup_index(&mut self, index: TyperIndex) -> Option<Arc<Ty<N, TyVar>>> {
        match index {
            TyperIndex::Uid(uid) => self.local_var_types.get(&uid).cloned(),
            TyperIndex::Res(res) => todo!(),
        }
    }

    fn lower_params(
        &mut self,
        params: &[Spanned<bound::Parameter<N>>],
    ) -> SpanSeq<ast::Parameter<N>> {
        todo!()
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
        ty: &Arc<TyMatrix<N, TyVar>>,
    ) -> Option<Arc<TyMatrix<N, TyVar>>>
    where
        N: TryGetRes + Clone,
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
                            .map(|(param, arg)| {
                                let ty_var = self.get_or_assign_var(param.id);
                                (ty_var, arg.clone())
                            })
                            .collect();

                        let rhs_matrix = self.rebind(rhs_ty).matrix.clone();
                        apply_substitution(&substitution, rhs_matrix)
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
        value: Arc<TyMatrix<N, TyVar>>,
    ) -> UnitResult<N>
    where
        N: NameEquiv,
    {
        if !occurs_check(&var, value.as_ref()) {
            self.assign_var(var, value);
            Ok(())
        } else {
            Err(TypingError::OccursIn(var, value))
        }
    }

    fn assign_var(&mut self, var: TyVar, ty: Arc<TyMatrix<N, TyVar>>)
    where
        N: NameEquiv,
    {
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

    fn instantiate(&mut self, ty: &Ty<N, TyVar>) -> Arc<TyMatrix<N, TyVar>>
    where
        N: Clone,
    {
        let mut substitution = HashMap::default();

        for &var in &ty.prefix {
            substitution.insert(var, Arc::new(TyMatrix::Var(self.fresh_var())));
        }

        apply_substitution(&substitution, ty.matrix.clone())
    }

    fn zonk(&mut self, ty: &Ty<N, TyVar>) -> Arc<Ty<N, TyVar>>
    where
        N: Clone,
    {
        let matrix = self.zonk_matrix(ty.matrix.clone());
        Arc::new(Ty {
            prefix: ty.prefix.clone(),
            matrix,
        })
    }

    fn zonk_matrix(
        &mut self,
        matrix: Arc<TyMatrix<N, TyVar>>,
    ) -> Arc<TyMatrix<N, TyVar>>
    where
        N: Clone,
    {
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

    fn lookup_var(&mut self, var: TyVar) -> Option<Arc<TyMatrix<N, TyVar>>> {
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
    fn rebind(&mut self, ty: &Ty<N, Uid>) -> Arc<Ty<N, TyVar>>
    where
        N: Clone,
    {
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
        ty: &TyMatrix<N, Uid>,
    ) -> Arc<TyMatrix<N, TyVar>>
    where
        N: Clone,
    {
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

fn apply_substitution<N: Clone, V: Hash + Eq>(
    substitution: &HashMap<V, Arc<TyMatrix<N, V>>>,
    ty: Arc<TyMatrix<N, V>>,
) -> Arc<TyMatrix<N, V>> {
    match ty.as_ref() {
        TyMatrix::Prim(_) => ty,
        TyMatrix::Var(var) => substitution.get(var).cloned().unwrap_or(ty),
        TyMatrix::Tuple(elems) => Arc::new(ast::TyMatrix::Tuple(
            elems
                .iter()
                .cloned()
                .map(|ty| apply_substitution(substitution, ty))
                .collect(),
        )),
        TyMatrix::Named { name, args } => Arc::new(ast::TyMatrix::Named {
            name: name.clone(),
            args: args
                .iter()
                .cloned()
                .map(|ty| apply_substitution(substitution, ty))
                .collect(),
        }),
        TyMatrix::Fn { domain, codomain } => Arc::new(ast::TyMatrix::Fn {
            domain: domain
                .iter()
                .cloned()
                .map(|ty| apply_substitution(substitution, ty))
                .collect(),
            codomain: apply_substitution(substitution, codomain.clone()),
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
