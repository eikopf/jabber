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
        common::ViSp,
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

    pub fn unify(&mut self, t1: Arc<Ty<N, TyVar>>, t2: Arc<Ty<N, TyVar>>) {
        let res = self.unify_matrices(t1.matrix.clone(), t2.matrix.clone());

        if let Err(error) = res {
            self.errors.push(error);
        }
    }

    // TODO: finish implementing unification

    fn unify_matrices(
        &mut self,
        t1: Arc<TyMatrix<N, TyVar>>,
        t2: Arc<TyMatrix<N, TyVar>>,
    ) -> UnitResult<N> {
        match (t1.as_ref(), t2.as_ref()) {
            (TyMatrix::Prim(p1), TyMatrix::Prim(p2)) if p1 == p2 => Ok(()),
            (TyMatrix::Var(v1), TyMatrix::Var(v2)) => {
                self.unifier.union(*v1, *v2);
                Ok(())
            }
            (_, TyMatrix::Var(var)) => self.unify_var_value(*var, t1),
            (TyMatrix::Var(var), _) => self.unify_var_value(*var, t2),
            _ => Err(TypingError::DidNotUnify(t1, t2)),
        }
    }

    fn unify_var_value(
        &mut self,
        var: TyVar,
        value: Arc<TyMatrix<N, TyVar>>,
    ) -> UnitResult<N> {
        if !occurs_check(&var, value.as_ref()) {
            self.assign_var(var, value);
            Ok(())
        } else {
            Err(TypingError::OccursIn(var, value))
        }
    }

    fn assign_var(&mut self, var: TyVar, ty: Arc<TyMatrix<N, TyVar>>) {
        // grab the representative element for `var`.
        let repr = self.unifier.find(var);

        // check for a preexisting assignment
        if let Some(current_ty) = self.lookup_var(repr) {
            // unify to check consistency with current_ty
            self.unify(current_ty, Ty::unquantified(ty));
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
