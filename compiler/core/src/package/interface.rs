//! Serializable package interface types.

// the types in this module are modelled on similar types in gleam's
// `compiler_core::package_interface` module. they are used by the compiler
// to talk about packages and their members after they have been compiled, and
// without having to keep all packages in memory simultaneously

use std::collections::HashMap;

use semver::{Version, VersionReq};

pub struct Package {
    name: Box<str>,
    version: Version,
    language_req: Option<VersionReq>,
    /// The modules in this package.
    ///
    /// Note that the names of modules are not broken up by element, so e.g. a
    /// module `core.foo.bar` would use the key `foo.bar` in this map.
    modules: HashMap<Box<str>, Module>,
}

pub struct Module {
    types: HashMap<Box<str>, TypeDef>,
    terms: HashMap<Box<str>, TermDef>,
}

pub enum TypeDef {
    Alias(TypeAliasDef),
    Extern,
    Adt,
}

pub struct TypeAliasDef {
    params: Box<[Box<str>]>,
    ty: Ty,
}

pub struct TermDef;

type Ty = ();

pub struct AdtDef {
    name: Box<str>,
    package: Box<str>,
    module: Box<str>,
    parameters: Box<[Ty]>,
}
