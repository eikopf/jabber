//! Binary and library packages.

use std::path::Path;

use metadata::PackageKind;
use semver::Version;

pub mod loader;
pub mod metadata;

pub const JABBER_FILE_EXTENSION: &str = "jbr";
pub const PACKAGE_METADATA_FILE: &str = "jabber.toml";
pub const PACKAGE_SOURCE_DIR: &str = "src";

#[derive(Debug, Clone)]
pub struct Package<T, S = Box<str>> {
    pub name: S,
    pub kind: PackageKind,
    pub version: Version,
    pub source_path: Box<Path>,
    pub root_module: Module<T, S>,
}

#[derive(Debug, Clone)]
pub struct Module<T, S = Box<str>> {
    pub name: S,
    pub content: T,
    pub submodules: Box<[Self]>,
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

    pub fn collect_errs(self) -> Box<[Module<E, S>]> {
        todo!()
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
