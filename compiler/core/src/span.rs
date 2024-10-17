//! Types representing spans of source code.
//!
//! # Tree-sitter Source Types
//!
//! Tree-sitter reasons about source locations in terms of points and ranges. A
//! point is a pair of `usize` indices representing the row and column at a
//! source location, while a range is a pair of points _and_ a pair of byte
//! indices that denote the byte offsets at the start and end of the range.
//! Note that the end byte index is 1 byte _past_ the end of the range, and
//! that row and column indices begin at 0.

use std::{
    num::TryFromIntError,
    ops::{Deref, DerefMut},
};

/// A sequence of spanned values of `T`.
pub type SpanSeq<T> = Box<[Spanned<T>]>;

/// A spanned boxed value of `T`.
pub type SpanBox<T> = Box<Spanned<T>>;

/// A value of `T` together with its [`Span`] in the source.
///
/// This type implements [`Deref`] and [`DerefMut`] for `Target = T`, and so
/// methods on `&T` and `&mut T` can be called transparently on `&Spanned<T>`
/// and `&mut Spanned<T>`.
#[derive(Debug, Clone, Copy)]
pub struct Spanned<T> {
    pub item: T,
    pub span: Span,
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.item
    }
}

/// A half-open byte span in the source code.
#[derive(Debug, Clone, Copy)]
pub struct Span {
    pub start: u32,
    pub end: u32,
}

impl Span {
    /// Returns the length of the byte range represented by `self`. Note that
    /// this length is not necessarily the same as the number of characters in
    /// the byte range.
    pub fn length(&self) -> u32 {
        self.end - self.start
    }

    pub fn of<T>(self, value: T) -> Spanned<T> {
        Spanned {
            item: value,
            span: self,
        }
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.start, self.end)
    }
}

impl TryFrom<tree_sitter::Range> for Span {
    type Error = TryFromIntError;

    fn try_from(value: tree_sitter::Range) -> Result<Self, Self::Error> {
        let start: u32 = value.start_byte.try_into()?;
        let end: u32 = value.end_byte.try_into()?;

        Ok(Span { start, end })
    }
}
