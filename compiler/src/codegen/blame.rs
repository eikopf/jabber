//! Rendered code blame metadata.
//!
//! The [`Blame`] struct records a [`FileId`] and a [`Span`] in that file, while the [`Blamed`]
//! type annotates an arbitrary value with a [`Blame`].

use crate::{env::FileId, span::Span};

/// A spanned location in a particular file.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Blame {
    pub file: FileId,
    pub span: Span,
}

impl std::fmt::Debug for Blame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} in file {:?}", self.span, self.file.0)
    }
}

pub type BlameSeq<T> = Box<[Blamed<T>]>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Blamed<T> {
    item: T,
    blame: Blame,
}

impl<T> Blamed<T> {
    pub fn item(&self) -> &T {
        &self.item
    }

    pub fn unwrap(self) -> T {
        self.item
    }

    pub fn as_ref(&self) -> Blamed<&T> {
        Blamed {
            item: &self.item,
            blame: self.blame,
        }
    }
}

impl<T: std::fmt::Debug> std::fmt::Debug for Blamed<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#?} ({:?})", self.item, self.blame)
    }
}
