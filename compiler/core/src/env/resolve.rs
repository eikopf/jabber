//! Implementation of module-local name resolution.

use std::collections::HashMap;

use crate::{symbol::Symbol, unique::Uid};

use super::{import_res::ImportResEnv, Env, Res, ResError, ResWarning};

#[derive(Debug, Clone)]
pub struct Resolver {
    root_scope: Scope,
    scopes: Vec<Scope>,
}

#[derive(Debug, Clone)]
pub struct Scope {
    bindings: HashMap<Symbol, LocalRes>,
}

#[derive(Debug, Clone, Copy)]
pub enum LocalRes {
    Local { symbol: Symbol, id: Uid },
    Item(Res),
}

#[derive(Debug, Clone)]
pub enum LocalResError {}

#[derive(Debug, Clone)]
pub enum LocalResWarning {}

/// The main entrypoint for module-local name resolution.
pub fn resolve(
    Env {
        files,
        packages,
        modules,
        terms,
        types,
        interner,
    }: ImportResEnv,
    warnings: &mut Vec<ResWarning>,
    errors: &mut Vec<ResError>,
) -> Env {
    // we start by dumping most of the old environment into a new one, and
    // allocating new buffers with the right capacity for terms and types
    let mut env: Env = Env {
        files,
        packages,
        modules,
        interner,
        terms: Vec::with_capacity(terms.len()),
        types: Vec::with_capacity(types.len()),
    };

    // now we go over each term and type and linearly resolve the name they
    // use. we already have all the module scoped names available, so we
    // don't have to consider use-before-declaration problems: if a name
    // cannot be resolved, it is immediately an error

    // NOTE: it is *crucial* that we preserve the validity of TermId and
    // TypeId values into the given ImportResEnv, so we absolutely *cannot*
    // delete any terms or types. instead, we will mark them as malformed
    // and preserve as much information about them as possible

    for term in terms {
        todo!();
    }

    for ty in types {
        todo!();
    }

    // finally we just return the environment, since the caller owns the
    // `warnings` and `errors` buffers
    env
}
