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
//! `TODO: write about typechecking impl`

use std::{collections::HashMap, hash::Hash, sync::Arc};

use ena::unify::{InPlace, UnificationTable, UnifyKey};

use crate::{
    ast::{
        common::{NameEquiv, ViSp},
        typed::{self as ast, Ty, TyMatrix},
    },
    env::{Env, Res, resolve::BoundResult},
    span::Spanned,
    symbol::Symbol,
    unique::Uid,
};

pub mod lower;

pub type TypedEnv = Env<
    Spanned<ast::Term<BoundResult>>,
    Spanned<ast::Type<BoundResult>>,
    HashMap<Symbol, ViSp<Res>>,
>;

#[derive(Debug, Clone)]
pub enum TypingError<N> {
    DidNotUnify(Arc<TyMatrix<N, TyVar>>, Arc<TyMatrix<N, TyVar>>),
    OccursIn(TyVar, Arc<TyMatrix<N, TyVar>>),
}

// TODO: main entry point for typechecking

pub fn typecheck<N>(env: &TypedEnv) -> Result<(), Vec<TypingError<N>>> {
    let mut typer: Typer<'_, N> = Typer::new(env);

    for id in env.term_id_iter() {
        let term = env.get_term(id);
        todo!();
    }

    todo!();
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

pub struct Typer<'a, N> {
    env: &'a TypedEnv,
    errors: Vec<TypingError<N>>,
    unifier: UnificationTable<InPlace<TyVar>>,
    var_assignments: HashMap<TyVar, Arc<Ty<N, TyVar>>>,
    uid_assigments: HashMap<Uid, TyVar>,
    latest_index: u32,
}

type TyResult<N> = Result<Arc<Ty<N, TyVar>>, TypingError<N>>;
type UnitResult<N> = Result<(), TypingError<N>>;

impl<'a, N> Typer<'a, N> {
    pub fn new(env: &'a TypedEnv) -> Self {
        Self {
            env,
            errors: Default::default(),
            unifier: Default::default(),
            var_assignments: Default::default(),
            uid_assigments: Default::default(),
            latest_index: 0,
        }
    }

    pub fn check(
        &mut self,
        expr: &ast::Expr<N>,
        ty: Arc<Ty<N, TyVar>>,
    ) -> TyResult<N> {
        todo!()
    }

    pub fn infer(&mut self, expr: &ast::Expr<N>) -> TyResult<N> {
        todo!()
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
            assert!(self.unify(current_ty, Ty::unquantified(ty)).is_ok());
        } else {
            // otherwise just create the new assignment
            self.var_assignments.insert(repr, Ty::unquantified(ty));
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

    fn lookup_var(&mut self, var: TyVar) -> Option<Arc<Ty<N, TyVar>>> {
        let repr = self.unifier.find(var);
        self.var_assignments.get(&repr).cloned()
    }

    fn fresh_var(&mut self) -> TyVar {
        assert_ne!(self.latest_index, u32::MAX);

        self.latest_index += 1;
        TyVar(self.latest_index)
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
