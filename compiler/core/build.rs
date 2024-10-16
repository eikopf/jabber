use std::path::{Path, PathBuf};
use std::{env, fs};
use type_sitter_gen::{generate_nodes, tree_sitter};

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
        generate_nodes(path, &tree_sitter())
            .unwrap()
            .collapse() // this line doesn't appear in the type-sitter README
            .to_string(),
    )
    .unwrap();
}
