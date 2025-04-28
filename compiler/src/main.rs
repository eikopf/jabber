use std::path::PathBuf;

use clap::Parser;
use cli::{Cli, Command};

// executable-specific modules
mod cli;
mod driver;

// library modules
mod ast;
mod codegen;
mod cst;
mod env;
mod literal;
mod package;
mod source_file;
mod span;
mod symbol;
mod unique;

pub fn interface() -> driver::Result {
    let Cli {
        racket_bin,
        libs_path,
        command,
    } = Cli::parse();

    let racket_bin = match racket_bin {
        Some(path) => path,
        None => driver::find_racket_binary()?,
    };

    let context = driver::DriverContext {
        racket_bin,
        libs_root: libs_path,
    };

    match command {
        Command::Compile { input, output_dir } => {
            let input = match input {
                Some(input) => input,
                None => driver::default_input_path()?,
            };

            let output_dir = match output_dir {
                Some(path) => path,
                None => driver::default_output_dir(&input),
            };

            driver::compile_package(input, output_dir, &context)
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
