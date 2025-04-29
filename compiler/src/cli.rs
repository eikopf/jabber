//! CLI definitions and plumbing.

use std::path::Path;

use clap::{Parser, Subcommand};

#[derive(Debug, Parser)]
#[command(version, about, long_about = None)]
pub struct Cli {
    #[arg(short = 'b', long)]
    pub racket_bin: Option<Box<Path>>,
    #[arg(short = 'l', long)]
    pub libs_path: Box<Path>,
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Debug, Subcommand)]
pub enum Command {
    /// Compile a Jabber package
    Compile {
        #[arg(short = 'i', long)]
        input: Option<Box<Path>>,
        #[arg(short = 'o', long = "output")]
        output_dir: Option<Box<Path>>,
    },
    /// Execute a Jabber package
    Run {
        #[arg(short = 's', long)]
        support_path: Box<Path>,
        #[arg(short = 'i', long)]
        input: Option<Box<Path>>,
        #[arg(short = 'o', long = "output")]
        output_dir: Option<Box<Path>>,
    },
}
