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
    ast::{common::ViSp, typed as ast},
    env::{Env, Res, Term, TypeId, resolve::BoundResult},
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
pub enum TypingError {
    Overconstrained,
    Underconstrained,
}

// NOTE: the concrete thing that `typecheck` needs to do is to produce either a
// list of errors OR a set of assignments for unification variables so that we
// can replace those types directly in another pass

// TODO: main entry point for typechecking

pub fn typecheck(env: &TypedEnv) -> Result<(), Vec<TypingError>> {
    let mut typer = Typer {
        env,
        errors: Vec::new(),
        context: Default::default(),
    };

    for id in env.term_id_iter() {
        let term = env.get_term(id);
        typer.type_term(term);
    }

    todo!();
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct UnifVar(Uid);

impl From<Uid> for UnifVar {
    fn from(value: Uid) -> Self {
        Self(value)
    }
}

impl From<UnifVar> for Uid {
    fn from(value: UnifVar) -> Self {
        value.0
    }
}

impl std::fmt::Debug for UnifVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        <Uid as std::fmt::Debug>::fmt(&self.0, f)
    }
}

impl UnifyKey for UnifVar {
    type Value = ();

    fn index(&self) -> u32 {
        self.0.into()
    }

    fn from_index(u: u32) -> Self {
        assert!(u != 0);
        unsafe { UnifVar(Uid::from_raw(u)) }
    }

    fn tag() -> &'static str {
        "UnifVar"
    }
}

struct Typer<'a> {
    env: &'a TypedEnv,
    errors: Vec<TypingError>,
    context: UnificationTable<InPlace<UnifVar>>,
}

#[derive(Debug, Clone, Copy)]
enum CheckResult {
    Success,
    Failure,
}

type TyResult<T> = Result<T, TypingError>;

impl Typer<'_> {
    fn type_term(&mut self, term: &Term<Spanned<ast::Term<BoundResult, Uid>>>) {
        todo!()
    }

    fn check(
        &mut self,
        expr: &ast::Expr<BoundResult, Uid>,
        ty: Arc<ast::Ty<TypeId, Uid>>,
    ) -> TyResult<CheckResult> {
        todo!()
    }

    fn infer(
        &mut self,
        expr: &ast::Expr<BoundResult, Uid>,
    ) -> TyResult<Arc<ast::Ty<TypeId, Uid>>> {
        todo!()
    }
}
