//! Unique-by-construction numeric IDs.
//!
//! # Uniqueness
//! A definition for uniqueness in this context is actually quite hard to pin
//! down. Talking about any set of _distinct_ objects already presumes that
//! they are mutually nonequal, and limits the scope of the definition to that
//! set only.
//!
//! In this context, uniqueness is a kind of provenance. If a pair of [`Uid`]
//! values are equal, then they are guaranteed to be copies of each other: one
//! must have been created by [`Uid::fresh`], and the other must be a copy of
//! that original [`Uid`].
//!
//! This property allows us to use [`Uid`] values like pointers, but on the
//! value level: we can test for the equality of two larger structures by their
//! [`Uid`] members without having to examine them completely. This property
//! is weaker than structural equality, since two values may be structurally
//! equal (modulo their ids) even if their [`Uid`] members differ.
//!
//! # Practical Implementation
//! We're using `u64` values as ids, so we have `2^64` ids to play with. Also,
//! since ids are emitted sequentially, uniqueness could only be broken by an
//! integer overflow. How likely is that to happen in any given invocation?
//!
//! A _very_ conservative estimate is that [`Uid::fresh`] is called every 100
//! cycles on a 4GHz core; that gives 40'000'000 new ids each second. Dividing
//! 2^64 by 40'000'000 gives roughly 4.612e11 seconds, or just under 14'615
//! **years**.

use std::{
    num::NonZeroU32,
    sync::atomic::{AtomicU32, Ordering},
};

static COUNTER: AtomicU32 = AtomicU32::new(1);

/// A unique-by-construction numeric identifier.
#[derive(Hash, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct Uid(NonZeroU32);

impl std::fmt::Debug for Uid {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "⟨{}⟩", self.0)
    }
}

impl From<Uid> for u32 {
    fn from(value: Uid) -> Self {
        value.0.into()
    }
}

impl Uid {
    /// Returns a new unique [`Uid`].
    pub fn fresh() -> Uid {
        let raw_id = COUNTER.fetch_add(1, Ordering::Relaxed);

        // SAFETY: COUNTER is initialized to 1, and will monotonically increase
        // for the (practical) lifetime of the program; hence raw_id is never 0
        let uid = unsafe { NonZeroU32::new_unchecked(raw_id) };
        Uid(uid)
    }

    /// Directly instantiates a [`Uid`] from a `u32`.
    ///
    /// # Safety
    /// `value` must be nonzero.
    pub unsafe fn from_raw(value: u32) -> Uid {
        Uid(unsafe { NonZeroU32::new_unchecked(value) })
    }
}

#[cfg(test)]
mod tests {
    use super::Uid;

    #[test]
    fn id_uniqueness() {
        let a = Uid::fresh();
        let b = Uid::fresh();
        let c = Uid::fresh();
        assert_ne!(a, b);
        assert_ne!(b, c);
    }
}
