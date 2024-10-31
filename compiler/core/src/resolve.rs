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

use ecow::EcoString;

use crate::{
    ast::{bound, unbound},
    env::{DeclId, Env, FileId, Location, ModId, PkgId},
    span::{Span, SpanSeq, Spanned},
};

pub struct Resolver<'e> {
    env: &'e mut Env,
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
    NoSuchModule { location: Location, name: EcoString },
}

// NOTE: the Scope and ScopeKind types borrow from the design of
// rustc_resolve::late::Rib and rustc_resolve::late::RibKind

struct Scope {
    terms: HashMap<EcoString, Res>,
    types: HashMap<EcoString, Res>,
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
    Decl(DeclId),
    Mod(ModId),
    Local(bound::Ident),
}

type ResResult<T = Res> = Result<T, ResolverError>;

impl<'e> Resolver<'e> {
    fn resolve_expr(
        &mut self,
        expr: Spanned<unbound::Expr>,
    ) -> ResResult<Spanned<bound::Expr>> {
        match expr.item {
            unbound::Expr::Name(name) => {
                self.resolve_name_expr(expr.span.with(name))
            }
            unbound::Expr::Literal(literal_expr) => todo!(),
            unbound::Expr::List(elems) => todo!(),
            unbound::Expr::Tuple(elems) => todo!(),
            unbound::Expr::Paren(inner) => todo!(),
            unbound::Expr::Block(block) => todo!(),
            unbound::Expr::Record { name, fields, base } => todo!(),
            unbound::Expr::Field { item, field } => todo!(),
            unbound::Expr::Lambda { params, body } => todo!(),
            unbound::Expr::Call { callee, args } => todo!(),
            unbound::Expr::Prefix { operator, operand } => todo!(),
            unbound::Expr::Binary { lhs, operator, rhs } => todo!(),
            unbound::Expr::Match { scrutinee, arms } => todo!(),
            unbound::Expr::IfElse {
                condition,
                consequence,
                alternative,
            } => todo!(),
        }
    }

    fn resolve_name_expr(
        &mut self,
        name: Spanned<unbound::Name>,
    ) -> ResResult<Spanned<bound::Expr>> {
        // if `name` is a path, then there are two options: either
        // it is an actual path to a decl, or it is a field expression.
        // which it is depends on whether the path evaluates to a declaration
        // or a local variable

        match name.item {
            unbound::Name::Path(Some(qualifier), elems) => {
                // convert the qualifier into the starting module id
                let start_mod_id = match qualifier.item {
                    unbound::Qualifier::Super => self
                        .env
                        .get_parent_module_id(self.current_module)
                        .ok_or_else(|| {
                            ResolverError::UsedSuperInRootModule {
                                location: self.locate_span(qualifier.span),
                            }
                        })?,
                    unbound::Qualifier::Self_ => self.current_module,
                    unbound::Qualifier::Package => self
                        .env
                        .get_package(self.current_package)
                        .root_module_id(),
                };

                // TODO: we need to resolve each element of the path
                // in the scope of the directly preceding element

                // TODO: write a dedicated path-resolving function

                todo!()
            }
            unbound::Name::Path(None, elems) => todo!(),
            unbound::Name::Ident(ident) => {
                let expr = match self.resolve_ident_as_term(ident)? {
                    Res::Decl(decl_id) => Ok(bound::Expr::Decl(decl_id)),
                    Res::Local(ident) => Ok(bound::Expr::Ident(ident)),
                    Res::Mod(id) => Err(ResolverError::UsedModuleAsExpr {
                        location: self.locate_span(name.span),
                        id,
                    }),
                }?;

                Ok(name.span.with(expr))
            }
        }
    }

    /// Resolves the given `path` relative to the given `mod_id`.
    ///
    /// # Path Semantics
    /// Syntactically, a path is a sequence of identifiers, optionally
    /// preceded by a qualifying keyword (`self`, `super`, or `package`).
    ///
    /// Semantically, those identifiers must all be modules, except for the
    /// last, which may be a declaration. The only exception is for type
    /// declarations: the penultimate element of the path may refer to a
    /// type declaration if the final element of the path refers to a type
    /// constructor. We call the module-sequence the _prefix_ of the path,
    /// while the final non-module portion is called the _subject_.
    ///
    /// # Package Topology
    /// While a module can `pub use` any ordinary declaration, it is **not**
    /// permitted to reexport a module declaration. This ensures that there is
    /// a single unique path from the root module to any given submodule in a
    /// package.
    fn resolve_path_in_module(
        &mut self,
        path: SpanSeq<unbound::Ident>,
        mod_id: ModId,
    ) -> ResResult {
        // TODO: implement this function recursively, by looking
        // at the first element in `path` and acting appropriately.

        todo!()
    }

    fn resolve_ident_as_term(&mut self, ident: unbound::Ident) -> ResResult {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.terms.get(&ident.0))
            .cloned()
            .ok_or_else(|| ResolverError::MissingTerm(ident))
    }

    fn resolve_ident_as_type(&mut self, ident: unbound::Ident) -> ResResult {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.types.get(&ident.0))
            .cloned()
            .ok_or_else(|| ResolverError::MissingType(ident))
    }

    // UTILITY METHODS

    fn module_scope(&self) -> &Scope {
        self.scopes
            .iter()
            .rev()
            .find(|scope| matches!(scope.kind, ScopeKind::Module))
            .expect("The resolver must have at least one module scope.")
    }

    fn locate_span(&self, span: Span) -> Location {
        Location {
            file: self.current_file,
            span,
        }
    }
}
