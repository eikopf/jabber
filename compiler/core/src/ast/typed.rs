//! Typed ASTs derived from [bound ASTs][`super::bound`].
//!
//! # Terminology
//!
//! The words _term_ and _type_ are used as in the previous ASTs, where in
//! particular a _type_ is a particular kind of declaration rather than a
//! type in the mathematical sense.
//!
//! We instead use the shortened _ty_ (hence [`Ty`]) to refer to the proper
//! types to be inferred and checked by the compiler. These types do not
//! necessarily reflect any kind of syntactic information in the source code,
//! but are instead purely logical constructs used to reason about the code.

use std::{collections::HashMap, sync::Arc};

use crate::{
    env::{Res, TypeId},
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

pub use super::bound::{
    BindingId, Bound, CallExprKind, GlobalBinding, LiteralExpr, LocalBinding,
    Name, NameContent, Path, PathBinding, Pattern, ResAttr, Ty as TyAst,
    TyConstr, TyConstrPayload,
};

// DECLARATIONS

/// A type declaration.
///
/// Based on the value of `kind`, this struct will represent either an ADT,
/// a type alias, or an external type declaration.
#[derive(Debug, Clone)]
pub struct Type<N = Bound, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub params: Box<[LocalBinding]>,
    pub kind: TypeKind<N>,
}

/// The kind of a [`Type`] together with any specific elements belonging to
/// each kind.
#[derive(Debug, Clone)]
pub enum TypeKind<N = Bound> {
    Alias {
        rhs: Spanned<TyAst<N>>,
    },
    Adt {
        opacity: Option<Span>,
        constructors: HashMap<Symbol, Spanned<TyConstr<N>>>,
    },
    Extern,
}

#[derive(Debug, Clone)]
pub struct Term<N = Bound, V = Uid, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub ty: Ty<TypeId, V>,
    pub kind: TermKind<N, V>,
}

#[derive(Debug, Clone)]
pub enum TermKind<N = Bound, V = Uid> {
    Fn {
        params: SpanSeq<Parameter<N>>,
        return_ty: Option<Spanned<TyAst<N>>>,
        body: Spanned<Typed<Expr<N, V>, N, V>>,
    },
    ExternFn {
        params: SpanSeq<Parameter<N>>,
        return_ty: Option<Spanned<TyAst<N>>>,
    },
    Const {
        ty_ast: Option<Spanned<TyAst<N>>>,
        value: Spanned<Typed<Expr<N, V>, N, V>>,
    },
}

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr<N = Bound, V = Uid> {
    Name(N),
    Literal(LiteralExpr),
    List(TySpanSeq<Self, N, V>),
    Tuple(TySpanSeq<Self, N, V>),
    LetIn {
        lhs: Option<LetStmtLhs<N>>,
        rhs: TySpanBox<Self, N, V>,
        body: TyBox<Self, N, V>,
    },
    RecordConstr {
        name: N,
        fields: SpanSeq<RecordExprField<N, V>>,
        base: Option<TySpanBox<Self, N, V>>,
    },
    RecordField {
        item: TySpanBox<Self, N, V>,
        field: Spanned<Symbol>,
    },
    TupleField {
        item: TySpanBox<Self, N, V>,
        field: Spanned<Option<u32>>,
    },
    Lambda {
        annotation: Ty<TypeId, Uid>,
        params: SpanSeq<Parameter<N>>,
        body: TySpanBox<Self, N, V>,
    },
    Call {
        callee: TySpanBox<Self, N, V>,
        args: TySpanSeq<Self, N, V>,
        kind: CallExprKind,
    },
    Builtin {
        operator: Spanned<BuiltinOperator>,
        lhs: TySpanBox<Self, N, V>,
        rhs: TySpanBox<Self, N, V>,
    },
    Match {
        scrutinee: TySpanBox<Self, N, V>,
        arms: SpanSeq<MatchArm<N, V>>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordExprField<N = Bound, V = Uid> {
    pub field: Spanned<Symbol>,
    pub value: Spanned<Typed<Expr<N, V>, N, V>>,
}

/// The lefthand side of a `let` stmt, consisting of a pattern with an
/// optional type annotation.
#[derive(Debug, Clone)]
pub struct LetStmtLhs<N = Bound> {
    pub pattern: Spanned<Pattern<N>>,
    pub ty_ast: Option<Spanned<TyAst<N>>>,
}

/// A builtin operator.
#[derive(Debug, Clone, Copy)]
pub enum BuiltinOperator {
    LazyAnd,
    LazyOr,
    Mutate,
}

#[derive(Debug, Clone)]
pub struct MatchArm<N = Bound, V = Uid> {
    pub pattern: Spanned<Pattern<N>>,
    pub body: Spanned<Typed<Expr<N, V>, N, V>>,
}

// PATTERNS

#[derive(Debug, Clone)]
pub struct Parameter<N = Bound> {
    pub pattern: Spanned<Pattern<N>>,
    pub ty_ast: Option<Spanned<TyAst<N>>>,
}

// PROPER TYPES

pub type TySpanSeq<T, N, V> = SpanSeq<Typed<T, N, V>>;
pub type TySpanBox<T, N, V> = SpanBox<Typed<T, N, V>>;
pub type TyBox<T, N, V> = Box<Typed<T, N, V>>;

#[derive(Debug, Clone)]
pub struct Typed<T, N = Bound, V = Uid> {
    pub item: T,
    pub ty: Arc<Ty<N, V>>,
}

impl<T, N, V> std::ops::Deref for Typed<T, N, V> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

/// A prenex type consisting of universally quantified type variables and
/// a subject matrix.
#[derive(Debug, Clone)]
pub struct Ty<N = TypeId, V = Uid> {
    pub vars: Box<[V]>,
    pub matrix: TyMatrix<N, V>,
    pub poisoned: bool,
}

impl<N, V> Ty<N, V> {
    pub fn with<T>(self: &Arc<Self>, item: T) -> Typed<T, N, V> {
        Typed {
            item,
            ty: self.clone(),
        }
    }

    pub fn prim(ty: PrimTy) -> Self {
        Ty {
            matrix: TyMatrix::Prim(ty),
            vars: Default::default(),
            poisoned: false,
        }
    }
}

impl<N> Ty<N, Uid> {
    /// Returns a type consisting of a single unbound type variable
    /// guaranteed to not already be bound. Effectively, this is an
    /// existential type variable that can be freely unified.
    pub fn fresh_unbound() -> Self {
        let uid = Uid::fresh();
        Self {
            vars: Default::default(),
            matrix: TyMatrix::Var(uid),
            poisoned: false,
        }
    }

    pub fn fresh_unbound_tuple(len: usize) -> Self {
        let mut vars = Vec::with_capacity(len);
        let mut elems = Vec::with_capacity(len);

        for _ in 0..len {
            let uid = Uid::fresh();
            vars.push(uid);
            elems.push(TyMatrix::Var(uid));
        }

        Self {
            vars: vars.into_boxed_slice(),
            matrix: TyMatrix::Tuple(elems.into_boxed_slice()),
            poisoned: false,
        }
    }

    pub fn fresh_unbound_fn(arity: usize) -> Self {
        let mut vars = Vec::with_capacity(arity);
        let mut domain = Vec::with_capacity(arity);

        for _ in 0..arity {
            let uid = Uid::fresh();
            vars.push(uid);
            domain.push(TyMatrix::Var(uid));
        }

        let codomain = {
            let uid = Uid::fresh();
            vars.push(uid);
            TyMatrix::Var(uid)
        };

        Self {
            vars: vars.into_boxed_slice(),
            matrix: TyMatrix::Fn {
                domain: domain.into_boxed_slice(),
                codomain: Box::new(codomain),
            },
            poisoned: false,
        }
    }
}

/// The *matrix* of a type.
///
/// In a [`Ty`], the `matrix` is the portion of the type which does not
/// contain any universal quantifiers.
#[derive(Debug, Clone)]
pub enum TyMatrix<N = TypeId, V = Uid> {
    Prim(PrimTy),
    Var(V),
    Tuple(Box<[Self]>),
    List(Box<Self>), // technically not a primitive type
    Adt {
        name: N,
        args: Box<[Self]>,
    },
    Fn {
        domain: Box<[Self]>,
        codomain: Box<Self>,
    },
    Poison,
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

// ERRORS

#[derive(Debug, Clone)]
pub enum TyError {
    NoSuchName {
        name: Spanned<NameContent>,
        span: Span,
    },
    /// it is invalid to use tyvars as polytypes
    TyVarWithArgs { name: LocalBinding, span: Span },
}
