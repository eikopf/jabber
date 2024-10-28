//! The primary interface for loading packages from files.

use std::{
    fs::{self, ReadDir},
    path::Path,
};

use thiserror::Error;

use crate::source_file::SourceFile;

use super::{
    metadata::Metadata, JABBER_FILE_EXTENSION, PACKAGE_METADATA_FILE,
    PACKAGE_SOURCE_DIR,
};

/// An unprocessed Jabber package loaded from the filesystem.
#[derive(Debug, Clone)]
pub struct RawPackage {
    root: Box<Path>,
    metadata: Metadata,
    source_files: Box<[SourceFile]>,
}

impl RawPackage {
    pub fn load(
        root: impl Into<Box<Path>>,
    ) -> Result<RawPackage, PackageLoadError> {
        let root = root.into();
        let root_dir = fs::read_dir(&root)?;

        let mut source_files = Vec::new();
        let mut metadata = None;

        for entry in root_dir {
            let entry = entry?;
            let file_name = entry.file_name();

            if file_name
                .to_str()
                .is_some_and(|name| name == PACKAGE_SOURCE_DIR)
                && entry.file_type()?.is_dir()
            {
                collect_jabber_files(
                    fs::read_dir(entry.path())?,
                    &mut source_files,
                )?;
            }

            if file_name
                .to_str()
                .is_some_and(|name| name == PACKAGE_METADATA_FILE)
            {
                metadata =
                    Some(toml::from_str(&fs::read_to_string(entry.path())?)?);
            }
        }

        match metadata {
            None => Err(PackageLoadError::MissingMetadata(root)),
            Some(metadata) => Ok(Self {
                root,
                metadata,
                source_files: source_files.into_boxed_slice(),
            }),
        }
    }
}

/// Globs all the `.jbr` files inside `dir`, possibly recursively into
/// any subdirectories.
fn collect_jabber_files(
    dir: ReadDir,
    source_files: &mut Vec<SourceFile>,
) -> std::io::Result<()> {
    for entry in dir.filter_map(Result::ok) {
        if entry.file_type()?.is_dir() {
            collect_jabber_files(fs::read_dir(entry.path())?, source_files)?;
        } else if entry.path().extension().and_then(std::ffi::OsStr::to_str)
            == Some(JABBER_FILE_EXTENSION)
        {
            let source_file = SourceFile::new(entry.path())?;
            source_files.push(source_file);
        }
    }

    Ok(())
}

#[derive(Debug, Error)]
pub enum PackageLoadError {
    #[error("Failed to read the given path: {0}")]
    Io(#[from] std::io::Error),
    #[error("Failed to parse `jabber.toml`: {0}")]
    Toml(#[from] toml::de::Error),
    #[error("Could not find `jabber.toml` in {0}")]
    MissingMetadata(Box<Path>),
}

#[cfg(test)]
mod tests {
    use std::{path::PathBuf, str::FromStr};

    use crate::package::metadata::PackageKind;

    use super::*;

    #[test]
    fn load_jabber_core_lib() {
        let path = PathBuf::from_str("../../libs/core").unwrap();
        let raw_package = RawPackage::load(path).unwrap();

        assert_eq!(raw_package.metadata.package.name.as_ref(), "core");
        assert_eq!(raw_package.metadata.package.kind, PackageKind::Library);
        assert!(!raw_package.source_files.is_empty())
    }
}
