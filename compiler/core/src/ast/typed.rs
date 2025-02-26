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

use std::{collections::HashMap, fmt::Debug, sync::Arc};

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
    pub ty: Arc<Ty<N, V>>,
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
        annotation: Arc<Ty<N, V>>,
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

/// A type with names of type `N` and variables of type `V`. Recursive variants
/// are stored with [`Arc`] so cloning can be cheap during unification.
#[derive(Clone)]
pub enum Ty<N = TypeId, V = Uid> {
    /// A primitive type.
    Prim(PrimTy),
    /// An existentially-quantified type.
    Exists(V),
    /// A universally-quantified type.
    Forall(V),
    /// A product of at least two types.
    Tuple(Box<[Arc<Self>]>),
    /// An algebraic data type (ADT) with 0 or more arguments.
    Adt { name: N, args: Box<[Arc<Self>]> },
    /// A function type with a domain of arbitrary arity.
    Fn {
        domain: Box<[Arc<Self>]>,
        codomain: Arc<Self>,
    },
}

impl<N: Debug, V: Debug> Debug for Ty<N, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Ty::Prim(prim_ty) => write!(f, "{:?}", prim_ty),
            Ty::Exists(var) => write!(f, "∃{:?}", var),
            Ty::Forall(var) => write!(f, "∀{:?}", var),
            Ty::Tuple(items) => {
                let (first, tail) = items.split_first().unwrap();
                write!(f, "({:?}", first)?;

                for elem in tail {
                    write!(f, ", {:?}", elem)?;
                }

                write!(f, ")")
            }
            Ty::Adt { name, args } => {
                write!(f, "ADT({:?})", name)?;

                if let Some((first, tail)) = args.split_first() {
                    write!(f, "[{:?}", first)?;

                    for arg in tail {
                        write!(f, ", {:?}", arg)?;
                    }

                    write!(f, "]")?;
                }

                Ok(())
            }
            Ty::Fn { domain, codomain } => {
                match domain.as_ref() {
                    [] => write!(f, "()"),
                    [param] => {
                        if matches!(param.as_ref(), Ty::Tuple(_)) {
                            // tuples need special handling when they
                            // occur as unary function parameters
                            write!(f, "({:?},)", param)
                        } else {
                            write!(f, "{:?}", param)
                        }
                    }
                    [first, tail @ ..] => {
                        write!(f, "({:?}", first)?;

                        for param in tail {
                            write!(f, ", {:?}", param)?;
                        }

                        write!(f, ")")
                    }
                }?;

                write!(f, " -> {:?}", codomain)
            }
        }
    }
}

impl<N, V> Ty<N, V> {
    /// Annotates an item with `self`.
    pub fn with<T>(self: &Arc<Self>, item: T) -> Typed<T, N, V> {
        Typed {
            item,
            ty: self.clone(),
        }
    }
}

impl<N, V: std::hash::Hash + Eq> Ty<N, V> {
    /// Returns `true` if and only if `self` does not contain unquantified
    /// (i.e. existential) type variables.
    pub fn is_concrete(&self) -> bool {
        match self {
            Ty::Prim(_) | Ty::Forall(_) => true,
            Ty::Exists(_) => false,
            Ty::Tuple(items) => items.iter().all(|ty| ty.is_concrete()),
            Ty::Adt { name: _, args } => args.iter().all(|ty| ty.is_concrete()),
            Ty::Fn { domain, codomain } => {
                domain.iter().all(|ty| ty.is_concrete())
                    && codomain.is_concrete()
            }
        }
    }
}

impl<N> Ty<N, Uid> {
    pub fn fresh_unbound() -> Self {
        Self::Exists(Uid::fresh())
    }

    pub fn fresh_unbound_tuple(len: usize) -> Self {
        let mut elems = Vec::with_capacity(len);

        for _ in 0..len {
            let elem = Arc::new(Self::fresh_unbound());
            elems.push(elem);
        }

        Self::Tuple(elems.into_boxed_slice())
    }

    pub fn fresh_unbound_fn(arity: usize) -> Self {
        let mut domain = Vec::with_capacity(arity);

        for _ in 0..arity {
            let elem = Arc::new(Self::fresh_unbound());
            domain.push(elem);
        }

        Self::Fn {
            domain: domain.into_boxed_slice(),
            codomain: Arc::new(Self::fresh_unbound()),
        }
    }
}

/// A primitive type.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum PrimTy {
    Never,
    Unit,
    Bool,
    Char,
    String,
    Int,
    Float,
}

impl Debug for PrimTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Never => write!(f, "!"),
            Self::Unit => write!(f, "()"),
            Self::Bool => write!(f, "bool"),
            Self::Char => write!(f, "char"),
            Self::String => write!(f, "string"),
            Self::Int => write!(f, "int"),
            Self::Float => write!(f, "float"),
        }
    }
}
