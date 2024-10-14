use thiserror::Error;
use tree_sitter as ts;
use tree_sitter_jabber;

use crate::{cst::Decl, span::Span};

pub struct CstBuilder<'a> {
    source: &'a [u8],
    cursor: ts::TreeCursor<'a>,
    shebang: Option<Span>,
    decls: Vec<Decl>,
    errors: Vec<ParseError>,
    comments: Vec<Span>,
}

impl<'a> CstBuilder<'a> {
    pub fn new(source: &'a [u8], tree: &'a ts::Tree) -> Self {
        let cursor = tree.walk();

        Self {
            source,
            cursor,
            shebang: None,
            decls: Vec::new(),
            errors: Vec::new(),
            comments: Vec::new(),
        }
    }
}

#[derive(Debug, Clone, Copy, Error)]
pub enum ParseError {
    #[error("Missing {kind} in span {span}.")]
    Missing { span: Span, kind: &'static str },
    #[error("Error occurred in span {span}.")]
    Error { span: Span },
}

pub struct Parser {
    parser: ts::Parser,
}

impl Parser {
    pub fn new() -> Self {
        let mut parser = ts::Parser::new();
        parser
            .set_language(&tree_sitter_jabber::LANGUAGE.into())
            .expect("Failed to load Tree-sitter grammar for Jabber");

        Self { parser }
    }

    pub fn parse(&mut self, src: impl AsRef<[u8]>) -> ts::Tree {
        self.parser
            .parse(src, None)
            .expect("Failed to parse some input, probably due to a timeout")
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}
