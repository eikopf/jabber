//! File wrapper types and ingest utilities.

use std::{fs, io, path::Path, sync::Arc};

use crate::unique::Uid;

/// Creates a fake [`SourceFile`] with the given contents.
#[macro_export]
macro_rules! fake_file {
    ($s:expr) => {
        $crate::source_file::SourceFile::fake(
            $crate::source_file::FileName::Fake {
                file: file!(),
                line: line!(),
            },
            String::from($s),
        )
    };
}

/// A source file.
///
/// Source files are relatively cheap to clone, since they store their
/// contents as an `Arc<str>`. The most expensive part of the clone impl is
/// therefore usually the copying of the `path` (if it is [`FileName::Real`]).
#[derive(Clone)]
pub struct SourceFile {
    path: FileName,
    contents: Arc<str>,
    id: Uid,
}

impl SourceFile {
    pub fn new(path: impl Into<Box<Path>>) -> io::Result<Self> {
        let id = Uid::fresh();
        let path = path.into();
        let contents = fs::read_to_string(&path)?.into();
        let path = FileName::Real(path);

        Ok(Self { path, contents, id })
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn path(self) -> Option<Box<Path>> {
        match self.path {
            FileName::Real(path) => Some(path),
            FileName::Fake { .. } => None,
        }
    }

    pub fn path_ref(&self) -> Option<&Path> {
        match &self.path {
            FileName::Real(path) => Some(path),
            FileName::Fake { .. } => None,
        }
    }

    /// Creates a fake file with the given path and contents.
    ///
    /// Prefer using the [`fake_file!`] macro, since it generates a fake
    /// path based on the source location it's used in.
    #[allow(unused)]
    pub(crate) fn fake(path: FileName, contents: impl Into<Arc<str>>) -> Self {
        let id = Uid::fresh();
        let contents = contents.into();

        Self { path, contents, id }
    }
}

impl std::fmt::Debug for SourceFile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let contents =
            format!("... {{{:.3}KiB}}", (self.contents.len() as f64) / 1024f64);
        f.debug_struct("File")
            .field("path", &self.path)
            .field("contents", &contents)
            .field("id", &self.id)
            .finish()
    }
}

#[derive(Clone)]
pub enum FileName {
    Real(Box<Path>),
    Fake { file: &'static str, line: u32 },
}

impl std::fmt::Debug for FileName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Real(path) => write!(f, "{:?}", path),
            Self::Fake { file, line } => {
                write!(f, "{{fake file in {} (line {})}}", file, line)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn filename_debug_impl() {
        let real = FileName::Real(Path::new("/tmp/foo/bar").into());
        let fake = FileName::Fake {
            file: file!(),
            line: line!(),
        };

        dbg!(real);
        dbg!(fake);
    }
}
