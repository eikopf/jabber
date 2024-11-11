//! Name resolution

// # Some Vague Notes
//
// ## Paths
// Whenever we encounter a qualified name, we want to unqualify it. That seems
// obvious, but it informs the data structures we can use.
//
// ## Specific Problems
// This domain consists of two large problem areas.
//
// In the first area, we want to take all of our top-level declarations, merge
// them into a flat package representation, and return this to the caller.
//
// In the second area, we want to verify that all the names in the program are
// correct: they must refer to actual definitions.
//
// In the first context, we need the ability to send any path to a top-level
// declaration to the correct definition. In the second context, we need to
// both verify that names are well-used, and then to rename them such that
// any local ambiguities are removed.

use std::collections::HashMap;

use crate::{
    ast::{bound, unbound},
    env::{Env, FileId, Location, ModId, PkgId, TermId, TypeId},
    symbol::Symbol,
};

pub struct Resolver {
    //env: &'e mut Env<A, B>,
    current_file: FileId,
    current_module: ModId,
    current_package: PkgId,
    scopes: Vec<Scope>,
    errors: Vec<()>,
}

pub enum ResolverError {
    MissingTerm(unbound::Ident),
    MissingType(unbound::Ident),
    UsedModuleAsExpr { location: Location, id: ModId },
    UsedSuperInRootModule { location: Location },
    NoSuchModule { location: Location, name: Symbol },
}

// NOTE: the Scope and ScopeKind types borrow from the design of
// rustc_resolve::late::Rib and rustc_resolve::late::RibKind

struct Scope {
    terms: HashMap<Symbol, Res>,
    types: HashMap<Symbol, Res>,
    kind: ScopeKind,
}

enum ScopeKind {
    /// A normal scope with no extra restrictions.
    Normal,
    /// A function scope that can introduce type & term parameters.
    Fn,
    /// A module scope that can affect declaration visibility.
    Module,
}

/// The value produced when a name is successfully resolved.
#[derive(Debug, Clone)]
enum Res {
    Term(TermId),
    Type(TypeId),
    TyConstr { ty: TypeId, name: Symbol },
    Mod(ModId),
    Local(bound::Ident),
}
