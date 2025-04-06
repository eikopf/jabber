use std::path::{Path, PathBuf};
use std::{env, fs};
use type_sitter_gen::{generate_nodes, generate_queries, super_nodes};

fn main() {
    // common setup
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    println!("cargo::rerun-if-changed=build.rs");

    // rerun if tree-sitter-jabber changes
    println!("cargo::rerun-if-changed=../../tree-sitter-jabber");

    // generate CST nodes for jabber
    let path = Path::new("../../tree-sitter-jabber/src/node-types.json");
    fs::write(
        out_dir.join("nodes.rs"),
        generate_nodes(path).unwrap().into_string(),
    )
    .unwrap();

    // generate queries for CST analysis
    fs::write(
        out_dir.join("queries.rs"),
        generate_queries(
            "./queries",
            "../../tree-sitter-jabber",
            &super_nodes(),
            false,
        )
        .unwrap()
        .into_string(),
    )
    .unwrap();
}
