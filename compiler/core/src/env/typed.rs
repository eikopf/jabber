//! Implementation for lowering into a typed environment and then checking
//! and inferring types within it.
//!
//! # Phases
//! Typechecking is broken into two phases,
//! 1. _lowering_, and;
//! 2. _checking_.
//!
//! ## Checking
//! `TODO: write about typechecking impl`

use std::collections::HashMap;

use crate::{
    ast::common::ViSp,
    ast::typed as ast,
    env::{resolve::BoundResult, Env, Res},
    span::Spanned,
    symbol::Symbol,
};

pub mod lower;

pub type TypedEnv = Env<
    Spanned<ast::Term<BoundResult>>,
    Spanned<ast::Type<BoundResult>>,
    HashMap<Symbol, ViSp<Res>>,
>;

// TODO: figure out the basic architecture for typechecking and inference

// TODO: where does pattern processing happen? can i check for exhaustiveness
// and lower to a simpler pattern representation
