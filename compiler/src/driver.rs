//! Central plumbing between CLI commands and internal functions.

use std::{
    collections::HashMap,
    io::Write,
    path::{Path, PathBuf},
    process::Command,
};

use petgraph::graph::DiGraph;
use which::which;

use thiserror::Error;

use crate::{
    codegen,
    cst::Parser,
    env,
    package::{
        PACKAGE_METADATA_FILE, Package,
        loader::PackageLoadError,
        metadata::{Metadata, MetadataLoadError, PackageKind},
    },
    source_file::SourceFile,
    symbol::Symbol,
};

pub const THUNK_FILE_NAME: &str = "0thunk.rkt";

/// The public result type of the [`driver`] module.
///
/// [`driver`]: self
pub type Result<T = ()> = std::result::Result<T, Error>;

#[derive(Debug, Error)]
pub enum Error {
    #[error("could not find a racket binary in the $PATH")]
    CouldNotFindRacketBinary,
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("{0}")]
    MetadataLoad(#[from] MetadataLoadError),
    #[error("{0}")]
    PackageLoad(#[from] PackageLoadError),
    #[error("detected a dependency cycle: contains {0}")]
    DependencyCycle(Box<str>),
}

#[derive(Debug, Clone)]
pub struct Context {
    pub libs_root: Box<Path>,
    pub racket_bin: Box<Path>,
}

impl Context {
    pub fn execute_binary_package(
        &self,
        package_root: &Path,
        output_dir: &Path,
        support_path: &Path,
    ) -> Result {
        // HACK: gross check to see if the package is actually a binary
        let (md, _) = load_package_with_metadata(package_root)?;
        if md.package.kind == PackageKind::Library {
            panic!("tried to run a library package")
        }

        // compile the package
        self.compile_package(package_root, output_dir)?;

        let mut racket = Command::new(self.racket_bin.to_path_buf());
        let cmd = racket
            .arg("--search")
            .arg(package_root)
            .arg("--search")
            .arg(support_path.parent().unwrap())
            .arg(output_dir.join(THUNK_FILE_NAME));

        match cmd.output() {
            Ok(output) => {
                std::io::stdout().write_all(&output.stdout)?;
                Ok(())
            }
            Err(error) => Err(error.into()),
        }
    }

    pub fn compile_package(
        &self,
        package_root: &Path,
        output_dir: &Path,
    ) -> Result {
        // lazily load libraries and eagerly load root package
        let libs = self.find_library_roots()?;
        let (md, package) = load_package_with_metadata(package_root)?;

        // build map from names to library paths
        let libs = libs
            .map(|(metadata, path)| {
                (metadata.package.name, (path, metadata.dependencies))
            })
            .collect::<HashMap<_, _>>();

        let ordered_deps = toposort_dependencies(
            package.name.clone(),
            md.dependencies.keys().cloned(),
            libs.iter()
                .map(|(name, (_, deps))| (name.clone(), deps.keys().cloned())),
        )?;

        let mut env = env::unbound::UnboundEnv::new();
        let mut parser = Parser::new().unwrap();
        let mut pkg_symbols = HashMap::<Box<str>, Symbol>::new();
        let core_symbol = env.interner.intern_static("core");

        for dep in ordered_deps {
            if dep != package.name {
                let (path, deps) = &libs.get(&dep).unwrap();
                let contents = Package::load_files(path.clone()).unwrap();

                let dep_package = contents
                    .map_modules(|file| parser.parse(file))
                    .transpose()
                    .unwrap()
                    .map_modules(crate::ast::unbound::Ast::try_from)
                    .transpose()
                    .unwrap()
                    .map_modules(crate::ast::unbound_lowered::Ast::from);

                let deps = deps
                    .keys()
                    .map(|name| pkg_symbols.get(name).copied().unwrap())
                    .chain(Some(core_symbol).filter(|_| *dep != *"core"))
                    .collect();

                let (symbol, warnings, errors) =
                    env.consume_package(dep_package, deps);
                pkg_symbols.insert(dep, symbol);

                for warning in warnings {
                    eprintln!("WARN (package loader): {warning:?}");
                }

                if !errors.is_empty() {
                    for error in errors {
                        eprintln!("ERROR (package loader): {error:?}");
                    }

                    panic!("fatal error encountered");
                }
            }
        }

        let package = package
            .map_modules(|file| parser.parse(file))
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound::Ast::try_from)
            .transpose()
            .unwrap()
            .map_modules(crate::ast::unbound_lowered::Ast::from);

        let deps = md
            .dependencies
            .keys()
            .map(|name| pkg_symbols.get(name).copied().unwrap())
            .chain(std::iter::once(core_symbol))
            .collect();

        let (root_symbol, warnings, errors) =
            env.consume_package(package, deps);
        pkg_symbols.insert(md.package.name.clone(), root_symbol);

        for warning in warnings {
            eprintln!("WARN (package loader): {warning:?}");
        }

        if !errors.is_empty() {
            for error in errors {
                eprintln!("ERROR (package loader): {error:?}");
            }

            panic!("fatal error encountered");
        }

        // resolve imports
        let (env, errors) =
            env::import_res::ImportResEnv::from_unbound_env(env);

        if !errors.is_empty() {
            for error in errors {
                eprintln!("ERROR (import resolver): {error:?}");
            }

            panic!("fatal error encountered");
        }

        // build resolved env
        let mut warnings = Vec::new();
        let mut errors = Vec::new();
        let env = env::resolve::resolve(env, &mut warnings, &mut errors);

        // lower to typed env
        let mut env = match env::typed::typecheck(env) {
            Ok(env) => env,
            Err((_, errs)) => {
                dbg![errs];
                panic!()
            }
        };

        // render packages
        let mut lowerer = codegen::lower::Lowerer::new(&mut env);
        std::fs::create_dir_all(output_dir)?;

        for (name, symbol) in pkg_symbols {
            let output_path = output_dir.join(format!("{name}.rkt"));
            let mut output_file = std::fs::File::create(output_path)?;

            let kind = match name == md.package.name {
                true => md.package.kind,
                false => PackageKind::Library,
            };

            let lowered_pkg = lowerer.lower_package(symbol, kind);
            lowered_pkg.write(&mut output_file, &mut lowerer.env.interner)?;
        }

        // generate executable thunk if this is a binary package
        if md.package.kind == PackageKind::Binary {
            let name = &md.package.name;
            let mut file =
                std::fs::File::create(output_dir.join(THUNK_FILE_NAME))?;
            write!(
                &mut file,
                "#!r6rs\n(import (target {}))\n({}/main #f)",
                &name, &name
            )?;
        }

        Ok(())
    }

    pub fn find_library_roots(
        &self,
    ) -> Result<impl Iterator<Item = (Metadata, Box<Path>)>> {
        let lib_root = std::fs::read_dir(&self.libs_root)?;
        Ok(lib_root
            .into_iter()
            .filter_map(std::result::Result::ok)
            .filter_map(|entry| {
                let path = entry.path().into_boxed_path();
                let metadata = path.join(PACKAGE_METADATA_FILE);

                Metadata::load(metadata)
                    .map(|metadata| (metadata, path))
                    .ok()
            }))
    }
}

// UTILITY FUNCTIONS

/// Eagerly loads the package at `path` together with its metadata.
pub fn load_package_with_metadata(
    path: &Path,
) -> Result<(Metadata, Package<SourceFile>)> {
    let metadata = Metadata::load(path.join(PACKAGE_METADATA_FILE))?;
    let package = Package::load_files(path)?;
    Ok((metadata, package))
}

pub fn toposort_dependencies(
    package_name: Box<str>,
    package_dependencies: impl Iterator<Item = Box<str>>,
    libs: impl Iterator<Item = (Box<str>, impl Iterator<Item = Box<str>>)>,
) -> Result<Vec<Box<str>>> {
    // build dependency graph
    let mut dep_graph: DiGraph<Box<str>, ()> = DiGraph::new();

    // insert root package and core library as graph nodes
    let core_idx = dep_graph.add_node("core".into());
    let package_idx = dep_graph.add_node(package_name);
    dep_graph.add_edge(package_idx, core_idx, ());

    // add nodes and edges for the dependencies of the root package
    for dep in package_dependencies {
        let idx = dep_graph.add_node(dep);
        dep_graph.update_edge(package_idx, idx, ());
    }

    // add nodes and edges for each library
    for (lib, deps) in libs {
        let lib_idx = dep_graph.add_node(lib.clone());

        for dep in deps {
            let dep_idx = dep_graph.add_node(dep.clone());
            dep_graph.update_edge(lib_idx, dep_idx, ());
        }
    }

    match petgraph::algo::toposort(&dep_graph, None) {
        Ok(indices) => Ok(indices
            .into_iter()
            .map(|idx| dep_graph[idx].clone())
            .collect()),
        Err(cycle) => {
            Err(Error::DependencyCycle(dep_graph[cycle.node_id()].clone()))
        }
    }
}

/// Searches the `PATH` for a program called `racket`.
pub fn find_racket_binary() -> Result<Box<Path>> {
    which("racket")
        .map(PathBuf::into_boxed_path)
        .map_err(|_| Error::CouldNotFindRacketBinary)
}

pub fn default_input_path() -> Result<Box<Path>> {
    std::env::current_dir()
        .map(PathBuf::into_boxed_path)
        .map_err(|err| err.into())
}

/// Returns the default output directory relative to the `package_root`.
pub fn default_output_dir(package_root: &Path) -> Box<Path> {
    package_root.join("target").into_boxed_path()
}

/// Canonicalizes the given [`Path`].
pub fn canonicalize(path: &Path) -> Result<Box<Path>> {
    path.canonicalize()
        .map(PathBuf::into_boxed_path)
        .map_err(|err| err.into())
}
