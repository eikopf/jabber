//! The [`Env`] type and related definitions.

use semver::Version;

use crate::source_file::SourceFile;

use crate::ast::bound as ast;
use crate::span::{Span, Spanned};
use crate::symbol::{StringInterner, Symbol};

#[derive(Debug, Clone, Copy)]
pub struct Location {
    pub span: Span,
    pub file: FileId,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct TermId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct TypeId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct TypeConstrId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct FileId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct PkgId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct ModId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub enum Visibility {
    Pub,
    Priv,
}

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct Vis<T> {
    item: T,
    visibility: Visibility,
}

impl<T: std::ops::Deref> std::ops::Deref for Vis<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

impl<T> Vis<T> {
    pub fn unwrap(self) -> T {
        self.item
    }
}

// TODO: add support for unloaded files as a precursor
// to compiled package caching

/// The global environment for a given compiler session.
///
/// This struct basically acts as a faux-database for the compiler during name
/// resolution, and is divided into several "tables" for `files`, `packages`,
/// `modules`, `terms`, and `types`.
pub struct Env {
    files: Vec<SourceFile>,
    packages: Vec<Package>,
    modules: Vec<Module>,
    terms: Vec<Term>,
    types: Vec<Type>,
    type_constructors: Vec<TypeConstr>,
    symbols: StringInterner,
}

/// An entry in the `packages` table of an [`Env`].
pub struct Package {
    /// The name of the package, which is globally unique among all packages.
    name: Symbol,
    /// The version of this package.
    version: semver::Version,
    /// The root module in this package's module tree.
    root_module: ModId,
    /// The immediate dependencies of this package.
    dependencies: Box<[PkgId]>,
}

/// An entry in the `modules` table of an [`Env`].
pub struct Module {
    name: Symbol,
    parent: Option<ModId>,
    file: FileId,
    package: PkgId,
    submodules: Vec<Vis<ModId>>,
    terms: Vec<Vis<TermId>>,
    types: Vec<Vis<TypeId>>,
}

/// An entry in the `terms` table of an [`Env`].
pub struct Term {
    name: Symbol,
    module: ModId,
    ast: Spanned<ast::TermDecl>,
}

/// An entry in the `types` table of an [`Env`].
pub struct Type {
    name: Symbol,
    module: ModId,
    ast: Spanned<ast::TypeDecl>,
    constructors: Vec<TypeConstrId>,
}

pub struct TypeConstr {
    name: Symbol,
    ty: TypeId,
    kind: TypeConstrKind,
}

pub enum TypeConstrKind {
    Unit,
    Tuple,
    Record,
}

#[derive(Debug, Clone)]
pub enum RegistrationError {
    DuplicateTermName {
        name: Symbol,
        location: Location,
        conflict: TermId,
    },
    DuplicateTypeName {
        name: Symbol,
        location: Location,
        conflict: TypeId,
    },
    DuplicatePackage {
        name: Symbol,
    },
    DuplicateModule {
        name: Symbol,
        package: PkgId,
        parent: ModId,
    },
}

impl Env {
    // MUTATORS

    pub fn register_package(
        &mut self,
        name: Symbol,
        version: Version,
        root_file: FileId,
        dependencies: Box<[PkgId]>,
    ) -> Result<PkgId, RegistrationError> {
        // check for conflicting names
        if let Some(duplicate) =
            self.packages.iter().find(|package| package.name == name)
        {
            return Err(RegistrationError::DuplicatePackage { name });
        }

        // WARN: there's a circular dependency between the `root_module` field
        // in a Package and the `package` field in a Module, so we have to
        // create one of them in an invalid state first. doing this to the
        // pkg_id requires that nothing else can mutate self.packages until
        // this function returns
        let pkg_id = PkgId(self.packages.len());

        // register root module
        let empty_symbol = self.symbols.intern_static("");
        let root_module =
            self.register_module(empty_symbol, None, root_file, pkg_id)?;

        // register package
        let package = Package {
            name,
            version,
            root_module,
            dependencies,
        };
        self.packages.push(package);
        let id = pkg_id; // beyond this point `id` is a valid PkgId

        // return the id
        Ok(id)
    }

    pub fn register_module(
        &mut self,
        name: Symbol,
        parent: Option<ModId>,
        file: FileId,
        package: PkgId,
    ) -> Result<ModId, RegistrationError> {
        // check for duplicate name (sanity check, this should be impossible)
        let duplicate = parent
            .map(|id| {
                self.get_module(id)
                    .submodules
                    .iter()
                    .map(|&id| Vis::unwrap(id))
            })
            .and_then(|mut iter| {
                iter.find(|&id| self.get_module(id).name == name)
            });

        if duplicate.is_some() {
            return Err(RegistrationError::DuplicateModule {
                name,
                package,
                parent: parent.unwrap(),
            });
        }

        // register module
        let module = Module {
            name,
            parent,
            file,
            package,
            submodules: Vec::new(),
            terms: Vec::new(),
            types: Vec::new(),
        };
        self.modules.push(module);
        let id = ModId(self.modules.len() - 1);

        // return module id
        Ok(id)
    }

    pub fn register_term(
        &mut self,
        name: Symbol,
        module: ModId,
        ast: Spanned<ast::TermDecl>,
        visibility: Visibility,
    ) -> Result<TermId, RegistrationError> {
        // check for conflicting names
        self.check_term_ns_conflict(module, name)
            .map_err(|conflict| RegistrationError::DuplicateTermName {
                name,
                conflict,
                location: Location {
                    span: ast.span,
                    file: self.get_module(module).file,
                },
            })?;

        // register new term
        let term = Term { name, module, ast };
        self.terms.push(term);
        let id = TermId(self.terms.len() - 1);

        // associate the term with its module
        self.get_module_mut(module).terms.push(Vis {
            item: id,
            visibility,
        });

        // return the new id
        Ok(id)
    }

    pub fn register_type(
        &mut self,
        name: Symbol,
        module: ModId,
        ast: Spanned<ast::TypeDecl>,
        visibility: Visibility,
    ) -> Result<TypeId, RegistrationError> {
        // check for conflicting names
        self.check_type_ns_conflict(module, name)
            .map_err(|conflict| RegistrationError::DuplicateTypeName {
                name,
                conflict,
                location: Location {
                    span: ast.span,
                    file: self.get_module(module).file,
                },
            })?;

        // register new type with 0 constructors
        let ty = Type {
            name,
            module,
            ast,
            constructors: Vec::new(),
        };
        self.types.push(ty);
        let id = TypeId(self.types.len() - 1);

        // associate the type with its module
        self.get_module_mut(module).types.push(Vis {
            item: id,
            visibility,
        });

        // return the new id
        Ok(id)
    }

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

    pub fn get_module_mut(&mut self, id: ModId) -> &mut Module {
        self.modules
            .get_mut(id.0)
            .expect("Module IDs are valid by construction")
    }

    pub fn get_parent_module_id(&self, id: ModId) -> Option<ModId> {
        self.get_module(id).parent
    }

    pub fn get_parent_module(&self, id: ModId) -> Option<&Module> {
        self.get_parent_module_id(id).map(|id| self.get_module(id))
    }

    pub fn check_term_ns_conflict(
        &self,
        id: ModId,
        name: Symbol,
    ) -> Result<(), TermId> {
        let duplicate = self
            .get_module(id)
            .terms
            .iter()
            .map(|&id| Vis::unwrap(id))
            .find(|&term_id| self.get_term(term_id).name == name);

        // TODO: this doesn't handle locally-scoped type constructors

        match duplicate {
            Some(term_id) => Err(term_id),
            None => Ok(()),
        }
    }

    pub fn check_type_ns_conflict(
        &self,
        id: ModId,
        name: Symbol,
    ) -> Result<(), TypeId> {
        let duplicate = self
            .get_module(id)
            .types
            .iter()
            .map(|&id| Vis::unwrap(id))
            .find(|&type_id| self.get_type(type_id).name == name);

        match duplicate {
            Some(type_id) => Err(type_id),
            None => Ok(()),
        }
    }

    pub fn check_type_constr_ns_conflict(
        &self,
        ty: TypeId,
        name: Symbol,
    ) -> Result<(), TypeConstrId> {
        let duplicate = self
            .get_type(ty)
            .constructors
            .iter()
            .find(|&&id| self.get_type_constr(id).name == name)
            .cloned();

        match duplicate {
            Some(type_constr_id) => Err(type_constr_id),
            None => Ok(()),
        }
    }

    // DECLARATIONS

    pub fn get_term(&self, id: TermId) -> &Term {
        self.terms
            .get(id.0)
            .expect("Term IDs are valid by construction")
    }

    pub fn get_type(&self, id: TypeId) -> &Type {
        self.types
            .get(id.0)
            .expect("Type IDs are valid by construction")
    }

    pub fn get_type_constr(&self, id: TypeConstrId) -> &TypeConstr {
        self.type_constructors
            .get(id.0)
            .expect("Type constructor IDs are valid by construction")
    }
}

impl Package {
    pub fn root_module_id(&self) -> ModId {
        self.root_module
    }
}
