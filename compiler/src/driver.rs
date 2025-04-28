//! Central plumbing between CLI commands and internal functions.

use std::path::{Path, PathBuf};

use which::which;

use thiserror::Error;

/// The public result type of the [`driver`] module.
///
/// [`driver`]: self
pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug, Clone, Error)]
pub enum Error {
    #[error("could not find a racket binary in the $PATH")]
    CouldNotFindRacketBinary,
    #[error("could not find the path \"{0}\"")]
    CouldNotFindPath(Box<Path>),
    #[error("permissions denied when accessing the path \"{0}\"")]
    BadPermissionsOnPath(Box<Path>),
    #[error("permissions denied when trying to access the current path")]
    BadPermissionsForCurrentPathAccess,
}

#[derive(Debug, Clone)]
pub struct DriverContext {
    pub libs_root: Box<Path>,
    pub racket_bin: Box<Path>,
}

pub fn compile_package(
    package_root: impl AsRef<Path>,
    output_dir: impl AsRef<Path>,
    ctx: &DriverContext,
) -> Result {
    todo!()
}

/// Searches the `PATH` for a program called `racket`.
pub fn find_racket_binary() -> Result<Box<Path>> {
    which("racket")
        .map(PathBuf::into_boxed_path)
        .map_err(|_| Error::CouldNotFindRacketBinary)
}

pub fn default_input_path() -> Result<Box<Path>> {
    match std::env::current_dir() {
        Ok(path) => Ok(path.into_boxed_path()),
        Err(error) => match error.kind() {
            std::io::ErrorKind::PermissionDenied => {
                Err(Error::BadPermissionsForCurrentPathAccess)
            }
            // NOTE: it is inconceivable that any other kind of error could
            // occur; i'm frankly not even sure the PermissionDenied path could
            // ever execute
            _ => unreachable!(),
        },
    }
}

/// Returns the default output directory relative to the `package_root`.
pub fn default_output_dir(package_root: &Path) -> Box<Path> {
    package_root.join("target").into_boxed_path()
}
