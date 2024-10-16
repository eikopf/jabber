use thiserror::Error;
use tree_sitter as ts;
use tree_sitter_jabber;

use crate::{
    cst::{Attr, Attributes, Cst, Decl, DeclBody, Ident, Name, UseItem, Visibility},
    span::{Span, SpanSeq, Spanned},
};

#[derive(Clone)]
pub struct TreeVisitor<'a> {
    cursor: ts::TreeCursor<'a>,
    source: &'a [u8],
    comments: Vec<Span>,
}

impl<'a> TreeVisitor<'a> {
    pub fn new(tree: &'a ts::Tree, source: &'a [u8]) -> Self {
        let cursor = tree.walk();
        let comments = Vec::new();

        Self {
            cursor,
            source,
            comments,
        }
    }

    pub fn build_cst(mut self) -> Result<Cst, Vec<ParseError>> {
        assert_eq!(self.cursor.node().kind(), "source_file");
        let root = self.cursor.node();

        let mut errors = Vec::new();
        collect_errors(&mut self.cursor, &mut errors);

        if errors.is_empty() {
            self.cursor.reset(root);
        } else {
            return Err(errors);
        }

        // beyond this point, the tree is guaranteed to have
        // no errors or missing nodes.

        self.cursor.goto_first_child();

        let shebang = self.try_visit_shebang();
        let mod_comment = self.try_visit_mod_comment();

        let mut decls = Vec::new();
        loop {
            if let Some(decl) = self.visit_decl() {
                decls.push(decl)
            };

            if !self.cursor.goto_next_sibling() {
                break;
            }
        }

        Ok(Cst {
            shebang,
            mod_comment,
            decls: decls.into_boxed_slice(),
            comments: self.comments.into_boxed_slice(),
        })
    }

    fn try_visit_shebang(&mut self) -> Option<Span> {
        self.consume_comments();

        match self.current_node_kind() {
            "shebang" => Some(self.current_node_span()),
            _ => None,
        }
    }

    fn try_visit_mod_comment(&mut self) -> Option<Span> {
        self.consume_comments();

        match self.current_node_kind() {
            "module_comment" => Some(self.current_node_span()),
            _ => None,
        }
    }

    fn visit_decl(&mut self) -> Option<Decl> {
        let node = self.cursor.node();

        match node.kind() {
            "use_decl" => self.visit_use_decl(),
            _ => unreachable!("There are no other top-level node kinds"),
        }
    }

    fn visit_use_decl(&mut self) -> Option<Decl> {
        debug_assert_eq!(self.current_node_kind(), "use_decl");
        let use_decl = self.cursor.node();
        let span = span(use_decl);

        todo!()
    }

    fn collect_decl_properties(&mut self) -> (Option<Span>, Option<Attributes>, Visibility) {
        todo!()
    }

    fn visit_use_item(&mut self) -> Option<Spanned<UseItem>> {
        todo!()
    }

    fn visit_name(&mut self) -> Spanned<Name> {
        let span = self.current_node_span();

        span.of(match self.current_node_kind() {
            "ident" => Name::Ident(Ident),
            "path" => Name::Path(self.visit_path()),
            _ => unreachable!("There are no other kinds of name."),
        })
    }

    fn visit_path(&mut self) -> Box<[Spanned<Ident>]> {
        todo!()
    }

    fn visit_ident(&mut self) -> Spanned<Ident> {
        debug_assert_eq!(self.current_node_kind(), "ident");

        let span = self.current_node_span();
        span.of(Ident)
    }

    fn consume_comments(&mut self) {
        while self.cursor.node().kind() == "comment" {
            self.comments.push(self.current_node_span());
            self.cursor.goto_next_sibling();
        }
    }

    fn current_node_kind(&self) -> &'static str {
        self.cursor.node().kind()
    }

    fn current_node_span(&self) -> Span {
        span(self.cursor.node())
    }
}

fn span(node: ts::Node<'_>) -> Span {
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
            span: span(node),
            range: node.range(),
        });
    } else if node.is_missing() {
        errors.push(ParseError::Missing {
            span: span(node),
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
