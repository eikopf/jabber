//! Distinguished bound ASTs for attributes.

use crate::{ast::bound::LiteralExpr, span::SpanSeq, symbol::Symbol};

/// An attribute defining some compiler metadata.
#[derive(Debug, Clone)]
pub struct Attr<NN, NA> {
    pub name: NN,
    pub args: SpanSeq<AttrArg<NA>>,
}

/// The set of recognised attribute names.
#[derive(Debug, Clone, Copy)]
pub enum AttrName {
    Debug,
    External { lang: Symbol },
    Operator { operator: Symbol },
}

/// An argument to an attribute.
#[derive(Debug, Clone, Copy)]
pub enum AttrArg<N> {
    Name(N),
    Literal(LiteralExpr),
}
