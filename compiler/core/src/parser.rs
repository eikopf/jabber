use thiserror::Error;
use tree_sitter as ts;
use tree_sitter_jabber;

use crate::{
    cst::{Attr, Cst, Decl, Ident, Visibility},
    span::{Span, Spanned},
};

pub struct CstBuilder<'a> {
    source: &'a [u8],
    cursor: ts::TreeCursor<'a>,
    shebang: Option<Span>,
    module_comment: Option<Span>,
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
            module_comment: None,
            decls: Vec::new(),
            errors: Vec::new(),
            comments: Vec::new(),
        }
    }

    pub fn build(mut self) -> (Vec<ParseError>, Cst) {
        loop {
            self.process_top_level_node();

            match self.goto_next_sibling() {
                Some(()) => continue,
                None => break,
            }
        }

        let cst = Cst {
            shebang: self.shebang,
            mod_comment: self.module_comment,
            comments: self.comments.into(),
            decls: self.decls.into(),
        };

        (self.errors, cst)
    }

    fn goto_next_sibling(&mut self) -> Option<()> {
        self.consume_comments();

        match self.cursor.goto_next_sibling() {
            true => Some(()),
            false => None,
        }
    }

    fn goto_first_child(&mut self) -> Option<()> {
        match self.cursor.goto_first_child() {
            true => {
                self.consume_comments();
                Some(())
            }
            false => None,
        }
    }

    fn consume_comments(&mut self) {
        while self.cursor.node().kind() == "comment" {
            let span = self.current_node_span();
            self.comments.push(span);
            self.cursor.goto_next_sibling();
        }
    }

    fn process_top_level_node(&mut self) {
        match self.cursor.node().kind() {
            "module_comment" => self.process_module_commnent(),
            "shebang" => self.process_shebang(),
            "use_decl" => todo!(),
            "mod_decl" => todo!(),
            "type_decl" => todo!(),
            "extern_type_decl" => todo!(),
            "struct_decl" => todo!(),
            "enum_decl" => todo!(),
            "fn_decl" => todo!(),
            "extern_fn_decl" => todo!(),
            "const_decl" => todo!(),
            _ => unreachable!("No other top-level nodes can exist"),
        }
    }

    fn process_module_commnent(&mut self) {
        debug_assert_eq!(self.cursor.node().kind(), "module_comment");

        let span = self.current_node_span();
        self.module_comment = Some(span);
    }

    fn process_shebang(&mut self) {
        debug_assert_eq!(self.cursor.node().kind(), "shebang");

        let span = self.current_node_span();
        self.shebang = Some(span);
    }

    fn process_use_decl(&mut self) {
        debug_assert_eq!(self.cursor.node().kind(), "use_decl");

        assert!(self.goto_first_child().is_some());

        let doc_comment = todo!();
        let attributes = todo!();
        let visibility = todo!();

        todo!()
    }

    fn current_node_span(&self) -> Span {
        span(&self.cursor.node())
    }
}

fn span(node: &ts::Node<'_>) -> Span {
    node.range()
        .try_into()
        .expect("Encountered byte index larger than u32::MAX")
}

#[derive(Debug, Clone, Copy, Error)]
pub enum ParseError {
    #[error("Missing {kind} in span {span}.")]
    Missing {
        span: Span,
        range: ts::Range,
        kind: &'static str,
        parent: Option<&'static str>,
    },
    #[error("Error occurred in span {span}.")]
    Error { span: Span, range: ts::Range },
}

fn collect_errors(cursor: &mut ts::TreeCursor, errors: &mut Vec<ParseError>) {
    let node = cursor.node();

    if node.is_error() {
        errors.push(ParseError::Error {
            span: span(&node),
            range: node.range(),
        });
    } else if node.is_missing() {
        errors.push(ParseError::Missing {
            span: span(&node),
            range: node.range(),
            kind: node.kind(),
            parent: node.parent().map(|n| n.kind()),
        });
    }

    if cursor.goto_first_child() {
        loop {
            collect_errors(cursor, errors);

            if !cursor.goto_next_sibling() {
                break;
            }
        }

        cursor.goto_parent();
    }
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

#[cfg(test)]
mod tests {
    use crate::{
        parser::{collect_errors, ParseError},
        span::Span,
    };

    use super::Parser;

    const SRC1: &str = r#"

        #! a shebang line

        //! a module comment

        // a regular comment

        type Foo =

        "#;

    #[test]
    fn tree_sitter_prodding() {
        let mut parser = Parser::new();
        let tree = parser.parse(SRC1);
        let mut cursor = tree.walk();

        let mut errors = Vec::new();
        collect_errors(&mut cursor, &mut errors);

        let Span { start, end } = match errors[0] {
            ParseError::Error { span, .. } => span,
            ParseError::Missing { span, .. } => span,
        };

        let (start, end) = (start as usize, end as usize);

        dbg!(&SRC1[start..end]);
        dbg!(errors);

        assert!(false);
    }
}
