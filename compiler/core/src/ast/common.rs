//! Pervasive AST constructs that change infrequently.

use crate::span::Span;

#[derive(Debug, Clone, Copy)]
pub enum Qualifier {
    Super,
    Self_,
    Package,
}

#[derive(Debug, Clone, Copy, Default)]
pub enum Visibility {
    Pub(Span),
    #[default]
    Priv,
}
