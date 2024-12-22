//! The [`Env`] type and related definitions.

use std::collections::HashMap;

use import_res::{ImportResError, PrefixId};
use resolve::{LocalResError, LocalResWarning};
use unbound::{PackageIngestError, PackageIngestWarning};

use crate::{
    ast::{bound, common::ViSp},
    source_file::SourceFile,
    span::{Span, Spanned},
    symbol::{StringInterner, Symbol},
};

pub mod import_res;
pub mod resolve;
pub mod unbound;

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
pub struct ModId(usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Res {
    Term(TermId),
    Type(TypeId),
    /// A non-opaque ADT with a single constructor whose name is exactly the
    /// same as the name of the type.
    StructType(TypeId),
    TyConstr {
        ty: TypeId,
        name: Symbol,
    },
    Module(ModId),
}

impl Res {
    pub fn as_module(self) -> Option<ModId> {
        if let Self::Module(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_type(self) -> Option<TypeId> {
        match self {
            Self::Type(id) | Self::StructType(id) => Some(id),
            _ => None,
        }
    }

    pub fn as_prefix(self) -> Option<PrefixId> {
        match self {
            Res::Type(id) => Some(PrefixId::Type(id)),
            Res::Module(id) => Some(PrefixId::Mod(id)),
            _ => None,
        }
    }

    pub fn is_type(&self) -> bool {
        matches!(self, Res::Type(_) | Res::StructType(_))
    }

    pub fn is_term(&self) -> bool {
        matches!(self, Self::Term(..))
    }

    pub fn as_term(self) -> Option<TermId> {
        if let Self::Term(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub enum ResError {
    Ingest {
        package: Symbol,
        error: PackageIngestError,
    },
    ImportRes {
        package: Symbol,
        error: ImportResError,
    },
    LocalRes {
        package: Symbol,
        error: LocalResError,
    },
}

#[derive(Debug, Clone)]
pub enum ResWarning {
    Ingest {
        package: Symbol,
        warning: PackageIngestWarning,
    },
    LocalRes {
        package: Symbol,
        warning: LocalResWarning,
    },
}

// TODO: add support for unloaded files as a precursor
// to compiled package caching

/// The global environment for a given compiler session.
///
/// This struct basically acts as a faux-database for the compiler during name
/// resolution, and is divided into several "tables" for `files`, `packages`,
/// `modules`, `terms`, and `types`.
#[derive(Debug)]
pub struct Env<
    // TODO: these should change once type checking is implemented
    Te = bound::Term,
    Ty = bound::Type,
    I = HashMap<Symbol, ViSp<Res>>,
> {
    files: Vec<SourceFile>,
    packages: HashMap<Symbol, Package>,
    modules: Vec<Module<I>>,
    terms: Vec<Term<Te>>,
    types: Vec<Type<Ty>>,
    interner: StringInterner,
}

/// An entry in the `packages` table of an [`Env`].
#[derive(Debug, Clone)]
pub struct Package {
    /// The version of this package.
    version: semver::Version,
    /// The root module in this package's module tree.
    root_module: ModId,
    /// The immediate dependencies of this package.
    dependencies: Box<[Symbol]>,
}

/// An entry in the `modules` table of an [`Env`].
#[derive(Debug, Clone)]
pub struct Module<I> {
    name: Symbol,
    parent: Option<ModId>,
    file: FileId,
    package: Symbol,
    items: I,
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

/// A located [`Symbol`] in an [`Env`].
pub type Name = Loc<Symbol>;

/// A value of `T` annotated with its location in an [`Env`].
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Loc<T> {
    pub item: Spanned<T>,
    pub module: ModId,
}

impl<T: std::ops::Deref> std::ops::Deref for Loc<T> {
    type Target = Spanned<T>;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ResValue<'a, Te, Ty, V> {
    Term(&'a Term<Te>),
    Type(&'a Type<Ty>),
    StructType(&'a Type<Ty>),
    TyConstr { ty: &'a Type<Ty>, name: Symbol },
    Mod(&'a Module<HashMap<Symbol, V>>),
}

impl<Te, Ty> Env<Te, Ty, HashMap<Symbol, ViSp<Res>>> {
    // MAGIC METHODS

    /// Returns the [`ModId`] of a direct submodule of `core` (e.g. `core.ref`)
    /// if such a submodule exists.
    pub fn magic_core_submodule(&mut self, submodule: Symbol) -> Option<ModId> {
        let core = self.core_root_module();

        self.get_module(core)
            .items
            .get(&submodule)
            .map(|visp| visp.spread().2)
            .and_then(|res| res.as_module())
    }

    pub fn item_in_module(
        &mut self,
        item: Symbol,
        module: ModId,
    ) -> Option<Res> {
        let module = self.get_module(module);
        let (_, _, res) = module.items.get(&item)?.spread();
        Some(res)
    }
}

impl<Te, Ty, V> Env<Te, Ty, HashMap<Symbol, V>> {
    pub fn get_res(&self, res: Res) -> ResValue<'_, Te, Ty, V> {
        match res {
            Res::Term(term_id) => ResValue::Term(self.get_term(term_id)),
            Res::Type(type_id) => ResValue::Type(self.get_type(type_id)),
            Res::StructType(type_id) => {
                ResValue::StructType(self.get_type(type_id))
            }
            Res::TyConstr { ty, name } => ResValue::TyConstr {
                ty: self.get_type(ty),
                name,
            },
            Res::Module(mod_id) => ResValue::Mod(self.get_module(mod_id)),
        }
    }

    pub fn get_res_name(&self, res: Res) -> Symbol {
        match self.get_res(res) {
            ResValue::Term(Term { name, .. })
            | ResValue::Type(Type { name, .. })
            | ResValue::StructType(Type { name, .. })
            | ResValue::Mod(Module { name, .. }) => *name,
            ResValue::TyConstr { name, .. } => name,
        }
    }
}

impl<Te, Ty, I: Default> Env<Te, Ty, I> {
    pub fn new() -> Self {
        Self {
            files: Vec::new(),
            packages: HashMap::new(),
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
        dependencies: Box<[Symbol]>,
    ) -> Symbol {
        let name = self.interner.intern(name);
        let root_module = self.register_module("", None, root_file, name);

        let package = Package {
            version,
            root_module,
            dependencies,
        };

        self.packages.insert(name, package);
        name
    }

    pub fn register_module(
        &mut self,
        name: &str,
        parent: Option<ModId>,
        file: FileId,
        package: Symbol,
    ) -> ModId {
        let module = Module {
            name: self.interner.intern(name),
            parent,
            file,
            package,
            items: I::default(),
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
}

impl<Te, Ty, I> Env<Te, Ty, I> {
    pub fn get_root_module(&self, package: Symbol) -> &Module<I> {
        self.get_module(self.get_package(package).root_module)
    }

    pub fn get_package(&self, package: Symbol) -> &Package {
        self.packages
            .get(&package)
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

    pub fn get_term(&self, term: TermId) -> &Term<Te> {
        self.terms
            .get(term.0)
            .expect("Term IDs are valid by construction")
    }

    pub fn get_type(&self, ty: TypeId) -> &Type<Ty> {
        self.types
            .get(ty.0)
            .expect("Type IDs are valid by construction")
    }

    pub fn get_file(&self, file: FileId) -> SourceFile {
        self.files
            .get(file.0)
            .cloned()
            .expect("File IDs are valid by construction")
    }

    pub fn get_file_ref(&self, file: FileId) -> &SourceFile {
        self.files
            .get(file.0)
            .expect("File IDs are valid by construction")
    }

    pub fn intern_source_span_in_module(
        &mut self,
        module: ModId,
        span: Span,
    ) -> Result<Symbol, std::str::Utf8Error> {
        let file = self.get_module(module).file;
        self.intern_source_span_in_file(file, span)
    }

    pub fn intern_source_span_in_file(
        &mut self,
        file: FileId,
        Span { start, end }: Span,
    ) -> Result<Symbol, std::str::Utf8Error> {
        let start = start as usize;
        let end = end as usize;

        let file = self.get_file(file);
        let bytes = &file.contents().as_bytes()[start..end];

        std::str::from_utf8(bytes).map(|s| self.interner.intern(s))
    }

    pub fn core_root_module(&mut self) -> ModId {
        let core = self.interner.intern_static("core");
        self.get_package(core).root_module
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
