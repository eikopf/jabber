//! Serializable package interface types.

// the types in this module are modelled on similar types in gleam's
// `compiler_core::package_interface` module. they are used by the compiler
// to talk about packages and their members after they have been compiled, and
// without having to keep all packages in memory simultaneously

use std::collections::HashMap;

use ecow::EcoString;
use semver::{Version, VersionReq};

pub struct Package {
    name: EcoString,
    version: Version,
    language_req: Option<VersionReq>,
    /// The modules in this package.
    ///
    /// Note that the names of modules are not broken up by element, so e.g. a
    /// module `core.foo.bar` would use the key `foo.bar` in this map.
    modules: HashMap<EcoString, Module>,
}

pub struct Module {
    types: HashMap<EcoString, TypeDef>,
    terms: HashMap<EcoString, TermDef>,
}

pub enum TypeDef {
    Alias(TypeAliasDef),
    Extern,
    Adt,
}

pub struct TypeAliasDef {
    params: Box<[EcoString]>,
    ty: Ty,
}

pub struct TermDef;

type Ty = ();

pub struct AdtDef {
    name: EcoString,
    package: EcoString,
    module: EcoString,
    parameters: Box<[Ty]>,
}
