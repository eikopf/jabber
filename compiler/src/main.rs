//! The Jabber compiler.

use clap::Parser;
use cli::{Cli, Command};

// executable-specific modules
pub mod cli;
pub mod driver;

// library modules
pub mod ast;
pub mod codegen;
pub mod cst;
pub mod env;
pub mod literal;
pub mod package;
pub mod source_file;
pub mod span;
pub mod symbol;
pub mod unique;

pub fn interface() -> driver::Result {
    let Cli {
        racket_bin,
        libs_path,
        command,
    } = Cli::parse();

    let racket_bin = match racket_bin {
        Some(path) => driver::canonicalize(&path)?,
        None => driver::find_racket_binary()?,
    };

    let libs_root = driver::canonicalize(&libs_path)?;

    let context = driver::Context {
        racket_bin,
        libs_root,
    };

    match command {
        Command::Compile { input, output_dir } => {
            let input = match input {
                Some(input) => driver::canonicalize(&input)?,
                None => driver::default_input_path()?,
            };

            let output_dir = match output_dir {
                Some(path) => driver::canonicalize(&path)?,
                None => driver::default_output_dir(&input),
            };

            context.compile_package(&input, &output_dir)
        }
        Command::Run {
            support_path,
            input,
            output_dir,
        } => {
            let support_path = driver::canonicalize(&support_path)?;

            let input = match input {
                Some(input) => driver::canonicalize(&input)?,
                None => driver::default_input_path()?,
            };

            let output_dir = match output_dir {
                Some(path) => driver::canonicalize(&path)?,
                None => driver::default_output_dir(&input),
            };

            context.execute_binary_package(&input, &output_dir, &support_path)
        }
    }
}

fn main() {
    match interface() {
        Ok(()) => (),
        Err(error) => {
            println!("{error}");
        }
    }
}
