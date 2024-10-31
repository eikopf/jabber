//! Binary and library packages.

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
