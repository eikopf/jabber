//! Lowered representations of types.
//!
//! We've already typechecked everything, so the only question is how we represent custom user
//! values at runtime. Following Idris' example, each value will be compiled as a vector whose
//! first element is a discriminant, with a variable number of elements in the tail. We don't
//! need to care about exactly _what_ types are in the tail, only how many there are per-variant.
//!
//! Let's consider some examples:
//! - `Option[!]` is _uninhabited_, and so it has no runtime representation. We consider this to be
//!   a kind of representation so we can erase matches.
//! - `Result[T, !]` is a _wrapper_ around a `T` value, so it inherits the representation of `T`.
//!   Note that this is *not true* for `Ref[T]`: because it has a mutable field it has reference
//!   semantics.
//! - `(A, B, C)` is a _struct_: it has only a single variant, so we can omit the discriminant
//!   field entirely.
//! - `Result[T, E]` doesn't fit into these categories, so we still have to insert discriminants to
//!   distinguish between variants.
//!
//! The reason that `Ref[T]` can't just be a wrapper type is the `mutable` annotation on its single
//! field. This gives the entire type reference semantics, and makes destructuring nontrivial. Note
//! that this applies only (up to isomorphism) to `Ref`, since the usual vector representation
//! already has reference semantics.

use std::num::NonZeroU32;

use crate::{ast::typed::PrimTy, env::TypeId};

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
#[derive(Debug, Clone)]
pub enum MonoTy {
    /// A tuple monotype with at least two [arguments].
    ///
    /// [arguments]: MonoArg
    Tuple(Box<[MonoArg]>),
    /// A named monotype.
    Named { name: TypeId, args: Box<[MonoArg]> },
    /// A function monotype.
    Fn {
        domain: Box<[MonoArg]>,
        codomain: MonoArg,
    },
}

/// An argument of a [monotype constructor].
///
/// [monotype constructor]: MonoTy
#[derive(Debug, Clone, Copy)]
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
    /// A primitive shape.
    Prim(PrimTy),
    /// Isomorphic to `core.ref.Ref[T]`.
    MutBox,
    /// Isomorphic to `core.list.List[T]`.
    List,
    /// Isomorphic to `core.option.Option`.
    Option,
    /// An external type whose contents are opaque.
    Extern { name: TypeId },
    /// A function reference of a fixed `arity`.
    Fn { arity: usize },
    /// A type with a single variant of a fixed `arity`.
    Struct { arity: usize },
    /// A type with several variants.
    Variants(Box<[Variant]>),
}

/// The runtime shape of a particular type variant.
///
/// Most variants will be [`Plain`]; this encompasses the vast majority of type constructors.
/// However, we distinguish some special variant shapes for particular analysis.
///
/// - The [`Cons`] variant denotes a tuple constructor with two fields and where the second field
///   is recursive; this is used to identify types which might be isomorphic to `core.list.List`.
/// - The [`Ref`] variant denotes a record constructor with a single mutable field, which is used
///   to identify types which might be isomorphic to `core.ref.Ref`.
///
/// [`Plain`]: Variant::Plain
/// [`Cons`]: Variant::Cons
/// [`Ref`]: Variant::Ref
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Variant {
    /// A tuple variant with two fields, the second of which is recursive.
    Cons,
    /// A record variant with a single mutable field.
    Ref,
    /// A variant with a fixed number of fields and no notable properties.
    Plain { arity: usize },
}

impl Variant {
    pub fn arity(&self) -> usize {
        match self {
            Variant::Cons => 2,
            Variant::Ref => 1,
            Variant::Plain { arity } => *arity,
        }
    }
}
