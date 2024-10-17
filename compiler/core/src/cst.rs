//! Concrete syntax trees parsed using Tree-sitter.

pub mod nodes {
    include!(concat!(env!("OUT_DIR"), "/nodes.rs"));
}

pub mod queries {
    include!(concat!(env!("OUT_DIR"), "/queries.rs"));
}

use nodes::SourceFile;
use type_sitter::{raw, Parser, Tree};

pub type Root = SourceFile<'static>;

/// Constructs a new [`Parser`] for Jabber, which can then be used to build
/// a [`Cst`] for some source code. Prefer using only one parser, as creating
/// a parser appears to involve loading the relevant language's dynamic
/// library at runtime.
pub fn create_jabber_parser() -> Result<Parser<Root>, raw::LanguageError> {
    Parser::new(&raw::Language::new(tree_sitter_jabber::LANGUAGE))
}

pub struct Cst {
    tree: Tree<Root>,
    source: String,
}

impl Cst {
    pub fn new(parser: &mut Parser<Root>, source: String) -> Self {
        let tree = parser
            .parse(source, None)
            .expect("Failed to build Cst, probably due to a parser timeout");

        todo!()
    }
}
