//! ASTs separated by compiler stage.

use crate::span::Span;

pub mod attr;
pub mod bound;
pub mod common;
pub mod unbound;
pub mod unbound_lowered;

#[derive(Debug, Clone)]
pub struct SpannedModuleTrivia {
    pub(self) shebang: Option<Span>,
    pub(self) module_comment: Option<Span>,
    pub(self) comments: Box<[Span]>,
}

impl SpannedModuleTrivia {
    pub fn new(
        shebang: Option<Span>,
        module_comment: Option<Span>,
        comments: Box<[Span]>,
    ) -> Self {
        Self {
            shebang,
            module_comment,
            comments,
        }
    }
}
