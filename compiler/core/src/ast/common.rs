//! Pervasive AST constructs that change infrequently.

use crate::span::{Span, Spanned};

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

impl Visibility {
    pub fn with<T>(self, item: T) -> Vis<T> {
        Vis {
            item,
            visibility: self,
        }
    }
}

pub type ViSp<T> = Vis<Spanned<T>>;

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
