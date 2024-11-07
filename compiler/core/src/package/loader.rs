//! The primary interface for loading packages from files.

use std::{
    fs::{self, DirEntry},
    path::Path,
};

use thiserror::Error;

use crate::source_file::SourceFile;

use super::{
    metadata::{Metadata, MetadataLoadError},
    Module, Package, JABBER_FILE_EXTENSION, PACKAGE_METADATA_FILE,
    PACKAGE_SOURCE_DIR,
};

impl Package<SourceFile> {
    pub fn load_files(
        root: impl Into<Box<Path>>,
    ) -> Result<Self, PackageLoadError> {
        let paths = Package::load_paths(root)?;
        let package = paths.map_modules(SourceFile::new);
        package.transpose().map_err(PackageLoadError::Io)
    }
}

#[derive(Debug, Error)]
pub enum PackageLoadError {
    #[error(transparent)]
    Path(#[from] PathLoadError),
    #[error("Failed to load all files in the package.")]
    Io(Package<Result<SourceFile, std::io::Error>>),
}

impl Package<Box<Path>> {
    pub fn load_paths(
        root: impl Into<Box<Path>>,
    ) -> Result<Self, PathLoadError> {
        let source_path = root.into();

        if !fs::metadata(&source_path)?.is_dir() {
            return Err(PathLoadError::PathIsNotDir(source_path));
        }

        let metadata = Metadata::load(source_path.join(PACKAGE_METADATA_FILE))?;
        let name = metadata.package.name;
        let kind = metadata.package.kind;
        let version = metadata.package.version;
        let root_module = load_module(
            "",
            kind.root_file_name(),
            source_path.join(PACKAGE_SOURCE_DIR),
        )?;

        Ok(Self {
            name,
            kind,
            version,
            source_path,
            root_module,
        })
    }
}

fn load_module(
    name: &str,
    root_file: impl AsRef<Path>,
    parent_dir: impl AsRef<Path>,
) -> Result<Module<Box<Path>>, PathLoadError> {
    let parent_dir = parent_dir.as_ref();
    let root_file = parent_dir.join(root_file);

    let mod_dir = parent_dir.join(name);
    let mut submodules = Vec::new();

    // if there is a submodule directory, load the modules it contains
    if let Ok(subdir_iter) = fs::read_dir(&mod_dir) {
        for path in subdir_iter.filter_map(|file| {
            file.ok()
                .filter(is_jabber_file)
                .map(|file| file.path())
                // this check prevents lib.jbr and bin.jbr from appearing as
                // their own submodules
                .filter(|path| path != &root_file)
        }) {
            let root_file = path.file_name().unwrap();
            let name = path.file_stem().unwrap().to_str().unwrap();
            let module = load_module(name, root_file, &mod_dir)?;
            submodules.push(module);
        }
    }

    Ok(Module {
        name: name.to_owned().into_boxed_str(),
        content: root_file.into_boxed_path(),
        submodules: submodules.into_boxed_slice(),
    })
}

fn is_jabber_file(entry: &DirEntry) -> bool {
    entry
        .path()
        .extension()
        .and_then(|os_str| os_str.to_str())
        .is_some_and(|ext| ext == JABBER_FILE_EXTENSION)
}

#[derive(Debug, Error)]
pub enum PathLoadError {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Metadata(#[from] MetadataLoadError),
    #[error("{0} is not a directory")]
    PathIsNotDir(Box<Path>),
}

#[cfg(test)]
mod tests {
    use std::{path::PathBuf, str::FromStr};

    use semver::Version;

    use crate::package::{metadata::PackageKind, Module, Package};

    #[test]
    fn load_jabber_core_lib() {
        // path loading
        let path = PathBuf::from_str("../../libs/core").unwrap();
        let package = Package::load_paths(path.clone()).unwrap();
        dbg!(&package);

        let Package {
            name,
            kind,
            version,
            source_path,
            root_module,
        } = package;

        assert_eq!(name.as_ref(), "core");
        assert_eq!(kind, PackageKind::Library);
        assert!(version > Version::new(0, 0, 0));
        assert_eq!(*source_path, path.as_ref());

        let Module {
            name, submodules, ..
        } = root_module;

        assert_eq!(name.as_ref(), "");
        assert!(submodules.len() > 4);

        // file loading
        let package = Package::load_files(path).unwrap();
        dbg!(&package);
    }
}
