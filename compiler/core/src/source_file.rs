//! File wrapper types and ingest utilities.

use std::{fs, io, path::Path};

use crate::unique::Uid;

#[derive(Clone)]
pub struct SourceFile {
    path: Box<Path>,
    contents: Box<str>,
    id: Uid,
}

impl SourceFile {
    pub fn new(path: impl Into<Box<Path>>) -> io::Result<Self> {
        let id = Uid::fresh();
        let path = path.into();
        let contents = fs::read_to_string(&path)?.into_boxed_str();
        Ok(Self { path, contents, id })
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn path(&self) -> &Path {
        &self.path
    }

    #[allow(unused)]
    pub(crate) fn fake(contents: impl Into<Box<str>>) -> Self {
        let id = Uid::fresh();
        let path = std::path::PathBuf::default().into_boxed_path();
        let contents = contents.into();

        Self { path, contents, id }
    }
}

impl std::fmt::Debug for SourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let contents = format!(
            "... {{{:.3}KiB}}",
            (self.contents.as_bytes().len() as f64) / 1024f64
        );
        f.debug_struct("File")
            .field("path", &self.path)
            .field("contents", &contents)
            .field("id", &self.id)
            .finish()
    }
}
