//! Types representing spans of source code.
//!
//! # Converting From Tree-sitter Types
//!
//! Tree-sitter reasons about source locations in terms of points and ranges. A
//! point is a pair of `usize` indices representing the row and column at a
//! source location, while a range is a pair of points _and_ a pair of byte
//! indices that denote the byte offsets at the start and end of the range.
//! Note that the end byte index is 1 byte _past_ the end of the range, and
//! that row and column indices begin at 0.
//!
//! In all, tree-sitter's `Range` type is 4 `usize` values tracking redundant
//! information, and we would like to avoid using them where possible.

use std::ops::{Deref, DerefMut};

/// A spanned sequence of spanned values of `T`.
pub type SpanSeq<T> = Spanned<Box<[Spanned<T>]>>;

/// A spanned boxed value of `T`.
pub type SpanBox<T> = Spanned<Box<T>>;

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
    pub start: SpanIndex,
    pub end: SpanIndex,
}

/// The integer type used for span indices.
type SpanIndex = u32;

impl Span {
    /// Returns the length of the byte range represented by `self`. Note that
    /// this length is not necessarily the same as the number of characters in
    /// the byte range.
    pub fn length(&self) -> SpanIndex {
        self.end - self.start
    }
}

impl std::fmt::Display for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.start, self.end)
    }
}
