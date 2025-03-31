//! Pervasive AST constructs that change infrequently.

use crate::span::{Span, Spanned};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
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

impl Visibility {
    pub fn with<T>(self, item: T) -> Vis<T> {
        Vis {
            item,
            visibility: self,
        }
    }
}

pub type ViSp<T> = Vis<Spanned<T>>;

impl<T> ViSp<T> {
    pub fn spread(self) -> (Visibility, Span, T) {
        let Vis {
            visibility,
            item: Spanned { item, span },
        } = self;
        (visibility, span, item)
    }
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Vis<T> {
    pub visibility: Visibility,
    pub item: T,
}

impl<T: std::ops::Deref> std::ops::Deref for Vis<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

impl<T> Vis<T> {
    pub fn unwrap(self) -> T {
        self.item
    }

    pub fn is_visible(&self) -> bool {
        matches!(self.visibility, Visibility::Pub(_))
    }

    pub fn public(item: T) -> Self {
        Visibility::Pub(Span::ZERO).with(item)
    }
}

/// Defines _equivalence_ of names for the implementing type.
pub trait NameEquiv<Rhs = Self> {
    /// Returns `true` iff `self` is equivalent to `rhs`.
    fn equiv(&self, rhs: &Rhs) -> bool;
}

impl<N, M> NameEquiv<Option<M>> for Option<N>
where
    N: NameEquiv<M>,
{
    fn equiv(&self, rhs: &Option<M>) -> bool {
        match (self, rhs) {
            (Some(lhs), Some(rhs)) => lhs.equiv(rhs),
            _ => false,
        }
    }
}

impl<N1, N2, E1, E2> NameEquiv<Result<N2, E2>> for Result<N1, E1>
where
    N1: NameEquiv<N2>,
{
    fn equiv(&self, rhs: &Result<N2, E2>) -> bool {
        match (self, rhs) {
            (Ok(lhs), Ok(rhs)) => lhs.equiv(rhs),
            _ => false,
        }
    }
}
