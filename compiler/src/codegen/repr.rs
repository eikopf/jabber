//! Lowered representations of types.
//!
//! NOTE: i have some open questions around this, mainly related to what idris2 does and why.
//! clearly i should erase singletons and uninhabited variants, and i need to maintain a record of
//! the canonical ordering among record fields, but how should this be done? also, i definitely
//! need to construct reprs for _monomorphic_ types, not generics: Result[!, !] is uninhabited,
//! whereas Result[(), !] is a singleton, and Result[(), ()] is isomorphic to bool.

use crate::env::{Location, TypeId};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ReprId(usize);

pub struct Repr {
    pub source: Location,
    pub type_id: TypeId,
    pub variants: Box<[Variant]>,
}

pub struct Variant {
    pub source: Location,
    pub members: Box<[Member]>,
}

pub enum Member {
    /// A recursive reference to the type itself.
    Rec,
    Bool,
    Char,
    String,
    Int,
    Float,
    List,
    Fn,
}
