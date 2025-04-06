//! Package metadata parsed from `.toml` files.

use std::{collections::HashMap, path::Path};

use semver::{Version, VersionReq};
use serde::{Deserialize, Serialize};
use thiserror::Error;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Metadata {
    pub package: PackageMetadata,
    pub language: Option<LanguageMetadata>,
    #[serde(default)]
    pub dependencies: HashMap<Box<str>, DepReq>,
}

#[derive(Debug, Error)]
pub enum MetadataLoadError {
    #[error(transparent)]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Toml(#[from] toml::de::Error),
}

impl Metadata {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, MetadataLoadError> {
        let file_contents = std::fs::read_to_string(&path)?;
        let metadata = toml::from_str(&file_contents)?;
        Ok(metadata)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename = "package")]
pub struct PackageMetadata {
    pub name: Box<str>,
    #[serde(rename = "type")]
    #[serde(default)]
    pub kind: PackageKind,
    pub version: Version,
}

#[derive(
    Debug, Default, Clone, Copy, PartialEq, Eq, Serialize, Deserialize,
)]
pub enum PackageKind {
    #[serde(rename = "bin")]
    #[serde(alias = "binary")]
    Binary,
    #[default]
    #[serde(rename = "lib")]
    #[serde(alias = "library")]
    Library,
}

impl PackageKind {
    pub const fn root_file_name(self) -> &'static str {
        match self {
            PackageKind::Binary => "bin.jbr",
            PackageKind::Library => "lib.jbr",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename = "language")]
pub struct LanguageMetadata {
    version: VersionReq,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DepReq {
    version: VersionReq,
    #[serde(flatten)]
    source: DepSource,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename = "source")]
pub enum DepSource {
    #[serde(rename = "git")]
    GitUrl,
    #[serde(rename = "path")]
    Path(Box<Path>),
}

#[cfg(test)]
mod tests {
    use super::{DepSource, Metadata, PackageKind};

    #[test]
    fn metadata_from_toml() {
        let source = r#"
        [package]
        name = "foobar"
        version = "0.1.0-dev"

        [dependencies]
        stuff  = { version = "1.0.32", path = "../stuff-module" }
        things = { version = "0.3.1-dev", path = "things-dev" }

        [language]
        version = "0.4"
        "#;

        let metadata: Metadata = toml::from_str(source).unwrap();
        let prerelease_dev = semver::Prerelease::new("dev").unwrap();

        assert_eq!(metadata.package.name.as_ref(), "foobar");
        assert!(matches!(metadata.package.kind, PackageKind::Library));

        assert_eq!(metadata.package.version.major, 0);
        assert_eq!(metadata.package.version.minor, 1);
        assert_eq!(metadata.package.version.patch, 0);
        assert_eq!(metadata.package.version.pre, prerelease_dev);

        let stuff = metadata.dependencies.get("stuff").unwrap();
        let things = metadata.dependencies.get("things").unwrap();

        assert!(matches!(stuff.source, DepSource::Path(_)));
        assert!(matches!(things.source, DepSource::Path(_)));
    }
}
