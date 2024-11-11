//! The [`Env`] type and related definitions.

use crate::package as pkg;
use crate::source_file::SourceFile;

use crate::ast::common::{ViSp, Vis};
use crate::ast::{bound, unbound_lowered as unbound};
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
pub struct FileId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct PkgId(usize);

#[derive(Debug, Hash, PartialEq, Eq, Clone, Copy)]
pub struct ModId(usize);

// TODO: add support for unloaded files as a precursor
// to compiled package caching

pub type BoundEnv = Env<bound::Term, bound::Type, ()>;
pub type UnboundEnv = Env<
    Spanned<unbound::Term>,
    Spanned<unbound::Type>,
    Vec<ViSp<unbound::Import>>,
>;

/// The global environment for a given compiler session.
///
/// This struct basically acts as a faux-database for the compiler during name
/// resolution, and is divided into several "tables" for `files`, `packages`,
/// `modules`, `terms`, and `types`.
#[derive(Debug)]
pub struct Env<Te, Ty, I> {
    files: Vec<SourceFile>,
    packages: Vec<Package>,
    modules: Vec<Module<I>>,
    terms: Vec<Term<Te>>,
    types: Vec<Type<Ty>>,
    interner: StringInterner,
}

/// An entry in the `packages` table of an [`Env`].
#[derive(Debug, Clone)]
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
#[derive(Debug, Clone)]
pub struct Module<I> {
    name: Symbol,
    parent: Option<ModId>,
    file: FileId,
    package: PkgId,
    imports: I,
    submodules: Vec<Vis<ModId>>,
    terms: Vec<Vis<TermId>>,
    types: Vec<Vis<TypeId>>,
}

/// An entry in the `terms` table of an [`Env`].
#[derive(Debug, Clone)]
pub struct Term<T> {
    name: Symbol,
    module: ModId,
    ast: T,
}

/// An entry in the `types` table of an [`Env`].
#[derive(Debug, Clone)]
pub struct Type<T> {
    name: Symbol,
    module: ModId,
    ast: T,
}

impl UnboundEnv {
    pub fn consume_package(
        &mut self,
        pkg::Package {
            name,
            version,
            root_module,
            ..
        }: pkg::Package<unbound::Ast>,
        dependencies: Box<[PkgId]>,
    ) -> PkgId {
        // register root file and package
        let root_file = self.register_file(root_module.content.file.clone());
        let package = self.register_package(
            name.as_ref(),
            version,
            root_file,
            dependencies,
        );

        // recursively populate table using module tree
        let root_module_id = self.get_package(package).root_module;
        self.populate_module(root_module, root_module_id, package);

        // return package id
        package
    }

    pub fn populate_module(
        &mut self,
        pkg::Module {
            name,
            content,
            submodules,
        }: pkg::Module<unbound::Ast>,
        mod_id: ModId,
        package: PkgId,
    ) {
        for module in submodules {
            // register file
            let file = self.register_file(module.content.file.clone());
            // register empty submodule
            let id = self.register_module(
                module.name.as_ref(),
                Some(mod_id),
                file,
                package,
            );
            // populate submodule
            self.populate_module(module, id, package);
        }

        let unbound::Ast {
            imports,
            terms,
            types,
            ..
        } = content;

        for import in imports {
            self.insert_import(import, mod_id);
        }

        for term in terms {
            self.insert_term(term, mod_id);
        }

        for ty in types {
            self.insert_type(ty, mod_id);
        }
    }

    pub fn insert_import(
        &mut self,
        import: ViSp<unbound::Import>,
        module: ModId,
    ) {
        let module = self.get_module_mut(module);
        module.imports.push(import);
    }

    pub fn insert_term(
        &mut self,
        Vis { visibility, item }: ViSp<unbound::Term>,
        module: ModId,
    ) {
        // get name in source
        let file = self.get_file(self.get_module(module).file);
        let name = item.name(file.contents().as_bytes());

        // register term in env table
        let term = self.register_term(name, module, item);

        // insert term into module
        let module = self.get_module_mut(module);
        module.terms.push(visibility.with(term));
    }

    pub fn insert_type(
        &mut self,
        Vis { visibility, item }: ViSp<unbound::Type>,
        module: ModId,
    ) {
        // get name in source
        let file = self.get_file(self.get_module(module).file);
        let name = item.name(file.contents().as_bytes());

        // register type in env table
        let ty = self.register_type(name, module, item);

        // insert type into module
        let module = self.get_module_mut(module);
        module.types.push(visibility.with(ty));
    }
}

impl<Te, Ty, I: Default> Env<Te, Ty, I> {
    pub fn new() -> Self {
        Self {
            files: Vec::new(),
            packages: Vec::new(),
            modules: Vec::new(),
            terms: Vec::new(),
            types: Vec::new(),
            interner: StringInterner::new(),
        }
    }

    pub fn register_package(
        &mut self,
        name: &str,
        version: semver::Version,
        root_file: FileId,
        dependencies: Box<[PkgId]>,
    ) -> PkgId {
        // WARN: this id is INVALID until the function returns, since we're
        // reserving an unallocated memory location.
        let package_id = PkgId(next_index(&self.packages));
        let root_module = self.register_module("", None, root_file, package_id);

        let package = Package {
            name: self.interner.intern(name),
            version,
            root_module,
            dependencies,
        };

        self.packages.push(package);
        package_id
    }

    pub fn register_module(
        &mut self,
        name: &str,
        parent: Option<ModId>,
        file: FileId,
        package: PkgId,
    ) -> ModId {
        let module = Module {
            name: self.interner.intern(name),
            parent,
            file,
            package,
            imports: I::default(),
            submodules: Vec::new(),
            terms: Vec::new(),
            types: Vec::new(),
        };

        self.modules.push(module);
        let raw_id = latest_index(&self.modules);
        ModId(raw_id)
    }

    pub fn register_file(&mut self, file: SourceFile) -> FileId {
        self.files.push(file);
        let raw_id = latest_index(&self.files);
        FileId(raw_id)
    }

    pub fn register_term(
        &mut self,
        name: &str,
        module: ModId,
        ast: Te,
    ) -> TermId {
        let term = Term {
            name: self.interner.intern(name),
            module,
            ast,
        };

        self.terms.push(term);
        let raw_id = latest_index(&self.terms);
        TermId(raw_id)
    }

    pub fn register_type(
        &mut self,
        name: &str,
        module: ModId,
        ast: Ty,
    ) -> TypeId {
        let ty = Type {
            name: self.interner.intern(name),
            module,
            ast,
        };

        self.types.push(ty);
        let raw_id = latest_index(&self.types);
        TypeId(raw_id)
    }

    // ACCESSORS

    pub fn get_root_module(&self, package: PkgId) -> &Module<I> {
        self.get_module(self.get_package(package).root_module)
    }

    pub fn get_package(&self, package: PkgId) -> &Package {
        self.packages
            .get(package.0)
            .expect("Package IDs are valid by construction")
    }

    pub fn get_module(&self, module: ModId) -> &Module<I> {
        self.modules
            .get(module.0)
            .expect("Module IDs are valid by construction")
    }

    pub fn get_module_mut(&mut self, module: ModId) -> &mut Module<I> {
        self.modules
            .get_mut(module.0)
            .expect("Module IDs are valid by construction")
    }

    pub fn get_file(&self, file: FileId) -> SourceFile {
        self.files
            .get(file.0)
            .cloned()
            .expect("File IDs are valid by construction")
    }
}

impl<Te, Ty, I: Default> Default for Env<Te, Ty, I> {
    fn default() -> Self {
        Self::new()
    }
}

fn latest_index<T>(slice: &[T]) -> usize {
    slice.len() - 1
}

fn next_index<T>(slice: &[T]) -> usize {
    slice.len()
}

#[cfg(test)]
mod tests {
    use std::{path::PathBuf, str::FromStr};

    use crate::cst::Parser;

    use super::*;

    #[test]
    fn build_unbound_env_from_core() {
        let path = PathBuf::from_str("../../libs/core").unwrap();
        let package = pkg::Package::load_files(path).unwrap();
        let mut parser = Parser::new().unwrap();

        let package = package
            .map_modules(|file| parser.parse(file))
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound::Ast::try_from)
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound_lowered::Ast::from);

        let mut env = UnboundEnv::new();
        let core_id = env.consume_package(package, Box::new([]));

        //dbg!(&env);

        for module in &env.modules {
            eprintln!("MOD: {}", env.interner.resolve(module.name).unwrap());
        }

        eprintln!(
            "PKG: {}",
            env.interner.resolve(env.get_package(core_id).name).unwrap()
        );

        //dbg!(&env.modules);
        dbg!(&env.modules[7].imports);

        panic!();
    }
}
