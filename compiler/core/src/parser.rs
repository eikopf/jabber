use tree_sitter as ts;
use tree_sitter_jabber as ts_jabber;

pub struct Parser {
    parser: ts::Parser,
}

impl Parser {
    pub fn new() -> Self {
        let mut parser = ts::Parser::new();
        parser
            .set_language(&ts_jabber::LANGUAGE.into())
            .expect("Failed to load Tree-sitter grammar for Jabber");

        Self { parser }
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}
