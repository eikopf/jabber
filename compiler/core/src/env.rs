use ecow::EcoString;

use crate::source_file::SourceFile;

use crate::ast::bound as ast;
use crate::span::{Span, Spanned};

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub span: Span,
    pub file: FileId,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct DeclId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct FileId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct PkgId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct ModId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum ModItemId {
    Mod(ModId),
    Decl(DeclId),
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum Visibility {
    Pub,
    Priv,
}

// TODO: add support for unloaded files as a precursor
// to compiled package caching

/// The global environment for a given compiler session.
///
/// This struct basically acts as a faux-database for the compiler during name
/// resolution, and is divided into several "tables" for `files`, `packages`,
/// `modules`, and `declarations`.
pub struct Env {
    files: Vec<SourceFile>,
    packages: Vec<Package>,
    modules: Vec<Module>,
    declarations: Vec<Decl>,
}

/// An entry in the `packages` table of an [`Env`].
pub struct Package {
    /// The name of the package, which is globally unique among all packages.
    name: EcoString,
    /// The version of this package.
    version: semver::Version,
    /// The root module in this package's module tree.
    root_module: ModId,
    /// The immediate dependencies of this package.
    dependencies: Box<[PkgId]>,
}

/// An entry in the `modules` table of an [`Env`].
pub struct Module {
    /// The name of this module as it would appear in a `mod` declaration.
    ///
    /// For package root modules, this field will be the empty string.
    name: EcoString,
    /// The parent of this module, which may be `None` in the case of package
    /// root modules.
    parent: Option<ModId>,
    /// The file in which this module is defined.
    file: FileId,
    /// The package in which this module is defined.
    package: PkgId,
    /// The items in this module (both submodules and declarations).
    items: Box<[(Visibility, ModItemId)]>,
}

/// An entry in the `declarations` table of an [`Env`].
pub struct Decl {
    /// The unqualified name of this declaration.
    name: EcoString,
    /// The module in which this declaration is defined. Note that this may be
    /// different than the module from which this declaration is accessed,
    /// since modules can publicly reexport declarations from one another.
    module: ModId,
    /// The AST of the declaration.
    ast: Spanned<ast::Decl>,
}

impl Env {
    // PACKAGES

    pub fn get_package(&self, id: PkgId) -> &Package {
        self.packages
            .get(id.0)
            .expect("Package IDs are valid by construction")
    }

    // MODULES

    pub fn get_module(&self, id: ModId) -> &Module {
        self.modules
            .get(id.0)
            .expect("Module IDs are valid by construction")
    }

    pub fn get_parent_module_id(&self, id: ModId) -> Option<ModId> {
        self.get_module(id).parent
    }

    pub fn get_parent_module(&self, id: ModId) -> Option<&Module> {
        self.get_parent_module_id(id).map(|id| self.get_module(id))
    }
}

impl Package {
    pub fn root_module_id(&self) -> ModId {
        self.root_module
    }
}

impl Module {
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    pub fn items(&self) -> &[(Visibility, ModItemId)] {
        self.items.as_ref()
    }

    pub fn public_items(&self) -> impl Iterator<Item = ModItemId> + use<'_> {
        self.items.iter().filter_map(|(vis, item)| {
            Some(*item).filter(|_| matches!(vis, Visibility::Pub))
        })
    }
}
