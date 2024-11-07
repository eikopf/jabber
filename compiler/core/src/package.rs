//! Binary and library packages.

use std::path::Path;

use metadata::PackageKind;
use semver::Version;

pub mod interface;
pub mod loader;
pub mod metadata;

const JABBER_FILE_EXTENSION: &str = "jbr";
const PACKAGE_METADATA_FILE: &str = "jabber.toml";
const PACKAGE_SOURCE_DIR: &str = "src";

// TODO: create iterator that does a topologically-ordered walk over the
// dependencies of a root package, while loading the files of each package
// into memory only once. this probably means that we first read only the
// `jabber.toml` files to identify dependencies, and build the ordering
// completely before passing it to an iterator

// NOTE: i presume (but do not know for sure) that `core` will be the terminal
// package for all dependency graphs. since this is probably true, it might be
// worth explicitly separating the "build core" stage of the compiler.

#[derive(Debug, Clone)]
pub struct Package<T, S = Box<str>> {
    name: S,
    kind: PackageKind,
    version: Version,
    source_path: Box<Path>,
    root_module: Module<T, S>,
}

#[derive(Debug, Clone)]
pub struct Module<T, S = Box<str>> {
    name: S,
    content: T,
    submodules: Box<[Self]>,
}

impl<T, S> Package<T, S> {
    pub fn map_modules<F, U>(self, mut f: F) -> Package<U, S>
    where
        F: FnMut(T) -> U,
    {
        Package {
            name: self.name,
            kind: self.kind,
            version: self.version,
            source_path: self.source_path,
            root_module: self.root_module.map(&mut f),
        }
    }
}

impl<T, E, S> Package<Result<T, E>, S> {
    /// If the module tree of `self` contains no errors, the results are
    /// unwrapped and `Ok(_)` is returned. If the module tree contains
    /// any errors, then `Err(self)` is returned with `self` unchanged.
    pub fn transpose(self) -> Result<Package<T, S>, Self> {
        match self.contains_err() {
            true => Err(self),
            false => {
                // SAFETY: this branch can only execute if self.contains_err
                // is false, so we can statically guarantee that unwrap would
                // never panic
                Ok(self.map_modules(|res| unsafe { res.unwrap_unchecked() }))
            }
        }
    }

    pub fn contains_err(&self) -> bool {
        self.root_module.contains_err()
    }
}

impl<T, S> Module<T, S> {
    pub fn map<F, U>(self, f: &mut F) -> Module<U, S>
    where
        F: FnMut(T) -> U,
    {
        let name = self.name;
        let content = f(self.content);
        let mut submodules = Vec::new();

        for module in self.submodules {
            submodules.push(module.map(f));
        }

        let submodules = submodules.into_boxed_slice();

        Module {
            name,
            content,
            submodules,
        }
    }
}

impl<T, E, S> Module<Result<T, E>, S> {
    pub fn contains_err(&self) -> bool {
        self.content.is_err()
            || self.submodules.iter().any(Module::contains_err)
    }
}
