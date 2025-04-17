//! Lowered representations of types.
//!
//! We've already typechecked everything, so the only question is how we represent custom user
//! values at runtime. Following Idris' example, each value will be compiled as a vector whose
//! first element is a discriminant, with a variable number of elements in the tail. We don't
//! need to care about exactly _what_ types are in the tail, only how many there are per-variant.
//!
//! Let's consider some examples:
//! - `Option[!]` is _uninhabited_, and so it has no runtime representation. We consider this to be
//!     a kind of representation so we can erase matches.
//! - `Result[T, !]` is a _wrapper_ around a `T` value, so it inherits the representation of `T`.
//!     Note that this is *not true* for `Ref[T]`: because it has a mutable field it has reference
//!     semantics.
//! - `(A, B, C)` is a _struct_: it has only a single variant, so we can omit the discriminant
//!     field entirely.
//! - `Result[T, E]` doesn't fit into these categories, so we still have to insert discriminants to
//!     distinguish between variants.
//!
//! The reason that `Ref[T]` can't just be a wrapper type is the `mutable` annotation on its single
//! field. This gives the entire type reference semantics, and makes destructuring nontrivial. Note
//! that this applies only (up to isomorphism) to `Ref`, since the usual vector representation
//! already has reference semantics.

use std::num::{NonZeroU32, NonZeroUsize};

use crate::{ast::typed::PrimTy, env::TypeId, symbol::Symbol};

/// A newtype ID referring to a [`MonoTy`].
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct MonoTyId(NonZeroU32);

impl MonoTyId {
    pub const MIN: Self = Self(NonZeroU32::MIN);

    pub fn increment(&mut self) {
        let inner = self.0.checked_add(1).unwrap();
        *self = Self(inner);
    }
}

/// A representable monotype.
///
/// This enum does not have a variant associated with functions because they do
/// not need any runtime representation analysis; for the purposes of this code
/// generator they are just opaque values.
pub enum MonoTy {
    /// A tuple monotype with at least two [arguments].
    ///
    /// [arguments]: MonoArg
    Tuple(Box<[MonoArg]>),
    /// A named monotype.
    Named { name: TypeId, args: Box<[MonoArg]> },
}

/// An argument of a [monotype constructor].
///
/// [monotype constructor]: MonoTy
pub enum MonoArg {
    /// A primitive type.
    Prim(PrimTy),
    /// The [ID] of a monotype.
    ///
    /// [ID]: MonoTyId
    Id(MonoTyId),
}

/// The runtime shape of a type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Shape {
    /// Isomorphic to `!`.
    Uninhabited,
    /// Isomorphic to `()`.
    Singleton,
    /// Isomorphic to `core.ref.Ref[T]`.
    MutBox,
    /// Isomorphic to `core.list.List[T]`.
    List,
    /// Isomorphic to `core.option.Option`.
    Option,
    /// A type with several variants.
    Variants(Box<[Variant]>),
}

/// The runtime shape of a particular type variant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Variant {
    Unit,
    Tuple { arity: NonZeroUsize },
    Record { fields: Box<[Symbol]> },
}
