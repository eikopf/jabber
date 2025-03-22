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

use std::{collections::HashMap, sync::Arc};

use ena::unify::{InPlace, UnificationTable, UnifyKey};

use crate::{
    ast::{
        common::ViSp,
        typed::{self as ast, Ty, TyMatrix},
    },
    env::{Env, Res, Term, resolve::BoundResult},
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
    DidNotUnify(Arc<TyMatrix<N>>, Arc<TyMatrix<N>>),
    OccursIn(Uid, Arc<TyMatrix<N>>),
}

// TODO: main entry point for typechecking

pub fn typecheck<N>(env: &TypedEnv) -> Result<(), Vec<TypingError<N>>> {
    let mut typer: Typer<'_, N> = Typer::new(env);

    for id in env.term_id_iter() {
        let term = env.get_term(id);
        typer.type_term(term);
    }

    todo!();
}

// WARNING: MASSIVE FUCKING PROBLEM ALERT
// the UnificationTable is backed by a contiguous vector, which is indexed by
// the values produced by `UnifyKey::index`. that means type variables _cannot_
// use `Uid`, and must instead be generated linearly strictly when necessary.
//
// NOTE: i think the solution here is probably not to alter the `lower`
// implementation again (thank fucking god), but just to process types from
// the `Uid` representation to a `TypeVar` representation during typechecking.

impl UnifyKey for Uid {
    type Value = ();

    fn index(&self) -> u32 {
        (*self).into()
    }

    fn from_index(u: u32) -> Self {
        assert!(u != 0);
        unsafe { Uid::from_raw(u) }
    }

    fn tag() -> &'static str {
        "Uid"
    }
}

pub struct Typer<'a, N> {
    env: &'a TypedEnv,
    errors: Vec<TypingError<N>>,
    assignments: HashMap<Uid, Arc<Ty<N>>>,
    unifier: UnificationTable<InPlace<Uid>>,
}

type TyResult<N> = Result<Arc<Ty<N>>, TypingError<N>>;
type UnitResult<N> = Result<(), TypingError<N>>;

impl<'a, N> Typer<'a, N> {
    pub fn new(env: &'a TypedEnv) -> Self {
        Self {
            env,
            errors: Default::default(),
            assignments: Default::default(),
            unifier: Default::default(),
        }
    }

    pub fn type_term(
        &mut self,
        term: &Term<Spanned<ast::Term<BoundResult, Uid>>>,
    ) {
        todo!()
    }

    pub fn check(
        &mut self,
        expr: &ast::Expr<N>,
        ty: Arc<Ty<N>>,
    ) -> TyResult<N> {
        todo!()
    }

    pub fn infer(&mut self, expr: &ast::Expr<N>) -> TyResult<N> {
        todo!()
    }

    pub fn unify(&mut self, t1: Arc<Ty<N>>, t2: Arc<Ty<N>>) {
        let res = self.unify_matrices(t1.matrix.clone(), t2.matrix.clone());

        if let Err(error) = res {
            self.errors.push(error);
        }
    }

    fn unify_matrices(
        &mut self,
        t1: Arc<TyMatrix<N>>,
        t2: Arc<TyMatrix<N>>,
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
        var: Uid,
        value: Arc<TyMatrix<N>>,
    ) -> UnitResult<N> {
        if !occurs_check(&var, value.as_ref()) {
            self.assign_var(var, value);
            Ok(())
        } else {
            Err(TypingError::OccursIn(var, value))
        }
    }

    fn assign_var(&mut self, var: Uid, matrix: Arc<TyMatrix<N>>) {
        // grab the representative element for `var`.
        let repr = self.unifier.find(var);

        // TODO: correct this to handle the case where `repr` has an
        // assignment, in which case it should be instantiated

        //let ty = Arc::new(Ty::unquantified(matrix));
        //self.assignments.insert(repr, ty);

        todo!()
    }

    fn instantiate(&self, ty: &Ty<N>) -> Arc<TyMatrix<N>>
    where
        N: Clone,
    {
        let mut substitution = HashMap::default();

        for &var in &ty.prefix {
            substitution.insert(var, Arc::new(TyMatrix::fresh_var()));
        }

        apply_substitution(&substitution, ty.matrix.clone())
    }

    fn lookup_var(&mut self, var: Uid) -> Option<Arc<Ty<N>>> {
        let repr = self.unifier.find(var);
        self.assignments.get(&repr).cloned()
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

fn apply_substitution<N: Clone>(
    substitution: &HashMap<Uid, Arc<TyMatrix<N>>>,
    ty: Arc<TyMatrix<N>>,
) -> Arc<TyMatrix<N>> {
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
