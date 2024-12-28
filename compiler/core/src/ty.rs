//! Canonical representations of types.
//!
//! The current implementation is geared towards bidirectional typechecking; in
//! particular we're following the Dunfield & Krishnaswami paper and a few
//! independent Haskell implementations.

use crate::unique::Uid;

/// A polytype.
#[derive(Debug, Clone)]
pub enum Ty {
    Forall(Uid, Box<Self>),
    Mono(MonoTy),
}

/// A monotype.
#[derive(Debug, Clone)]
pub enum MonoTy {
    Prim(PrimTy),
    Var(Uid),
    Exists(Uid),
    Fn(Box<[Ty]>, Box<Ty>),
}

/// A primitive type.
#[derive(Debug, Clone, Copy)]
pub enum PrimTy {
    Never,
    Unit,
    Bool,
    Char,
    String,
    Int,
    Float,
}
