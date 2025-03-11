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

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    hash::Hash,
    sync::Arc,
};

use crate::{
    env::{Res, TypeId, resolve::BoundResult},
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

pub use super::bound::{
    BindingId, Bound, CallExprKind, GlobalBinding, LiteralExpr, LocalBinding,
    Name, NameContent, Path, PathBinding, Pattern, ResAttr, Ty as TyAst,
    TyConstr as TyConstrAst,
};

// DECLARATIONS

/// A type declaration.
///
/// Based on the value of `kind`, this struct will represent either an ADT,
/// a type alias, or an external type declaration.
#[derive(Debug, Clone)]
pub struct Type<N = Bound, V = Uid, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub params: Box<[LocalBinding]>,
    pub kind: TypeKind<N, V>,
}

/// The kind of a [`Type`] together with any specific elements belonging to
/// each kind.
#[derive(Debug, Clone)]
pub enum TypeKind<N = Bound, V = Uid> {
    Alias {
        rhs_ast: Spanned<TyAst<N>>,
        rhs_ty: Arc<Ty<N, V>>,
    },
    Adt {
        opacity: Option<Span>,
        constrs: HashMap<Symbol, Spanned<TyConstr<N, V>>>,
    },
    Extern,
}

#[derive(Debug, Clone)]
pub struct TyConstr<N = Bound, V = Uid> {
    pub name: Spanned<Symbol>,
    pub ast: Spanned<TyConstrAst<N>>,
    pub kind: TyConstrKind<N, V>,
}

/// The kind of constructor, inferred during lowering from the [`super::bound`]
/// representation.
///
/// # Types
/// Because constructors may appear both as expressions and as patterns, it is
/// necessary to retain more information than just a single [`Ty`] can express.
///
/// ## Unit Constructors
/// The simplest constructors are unit constructors, so they hold a single
/// [`Arc`]-ed [`Ty`].
///
/// ## Tuple Constructors
/// When they are referred to by name, tuple constructors are simply ordinary
/// functions from their element types to their type. However, we also need to
/// retain the per-element types of tuple elements for use in patterns.
///
/// ## Record Constructors
/// When referred to by name, record constructors do not have a nameable type
/// (as opposed to unit and tuple constructors, which become constants and
/// functions respectively). We therefore only need to store the names and
/// types of the fields of the constructor for checking against record exprs
/// and record patterns.
#[derive(Debug, Clone)]
pub enum TyConstrKind<N = Bound, V = Uid> {
    /// A constant constructor.
    Unit(Arc<Ty<N, V>>),
    /// A record constructor.
    Record(HashMap<Symbol, RecordField<N, V>>),
    /// A tuple constructor.
    Tuple {
        /// The element types of the constructor.
        elems: Box<[Arc<Ty<N, V>>]>,
        /// The type of the constructor as a function. This is the type of the
        /// constructor when it is referred to by name, e.g. in a call expr.
        fn_ty: Arc<Ty<N, V>>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordField<N = Bound, V = Uid> {
    pub mutability: Option<Span>,
    pub name: Spanned<Symbol>,
    pub ty: Arc<Ty<N, V>>,
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
    /// A named type with 0 or more arguments.
    Named { name: N, args: Box<[Arc<Self>]> },
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
            Ty::Named { name, args } => {
                write!(f, "NAME({:?})", name)?;

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

    /// Returns `true` if and only if `self` does not contain unquantified
    /// (i.e. existential) type variables.
    pub fn is_concrete(&self) -> bool {
        match self {
            Ty::Prim(_) | Ty::Forall(_) => true,
            Ty::Exists(_) => false,
            Ty::Tuple(items) => items.iter().all(|ty| ty.is_concrete()),
            Ty::Named { name: _, args } => {
                args.iter().all(|ty| ty.is_concrete())
            }
            Ty::Fn { domain, codomain } => {
                domain.iter().all(|ty| ty.is_concrete())
                    && codomain.is_concrete()
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Binding {
    Universal,
    Existential,
}

impl<N, V: Eq> Ty<N, V> {
    /// Returns a [`Binding`] corresponding to how `var` is bound in `self`, or
    /// `None` if `var` does not occur in `self`. This function presumes that
    /// all occurrences of `var` are bound identically.
    pub fn binding_of(&self, var: &V) -> Option<Binding> {
        match self {
            Ty::Exists(v) if v == var => Some(Binding::Existential),
            Ty::Forall(v) if v == var => Some(Binding::Universal),
            Ty::Exists(_) | Ty::Forall(_) | Ty::Prim(_) => None,
            Ty::Tuple(elems) => elems.iter().find_map(|ty| ty.binding_of(var)),
            Ty::Named { name: _, args } => {
                args.iter().find_map(|ty| ty.binding_of(var))
            }
            Ty::Fn { domain, codomain } => domain
                .iter()
                .find_map(|ty| ty.binding_of(var))
                .or_else(|| codomain.binding_of(var)),
        }
    }
}

impl<N: Clone, V> Ty<N, V> {
    /// Returns the names in `self` for which `cmp` returns `true`.
    pub fn names_with<F>(&self, cmp: F) -> Vec<N>
    where
        F: Fn(&N) -> bool + Clone,
    {
        // HACK: this is a stupid and bad and stupid and dumb implementation
        // that allocates way too much; fix this later!!!!!
        match self {
            Ty::Prim(_) | Ty::Exists(_) | Ty::Forall(_) => vec![],
            Ty::Tuple(tys) => tys
                .iter()
                .flat_map(|ty| ty.names_with(cmp.clone()))
                .collect(),
            Ty::Named { name, args } => {
                let mut names = if cmp(name) {
                    vec![name.clone()]
                } else {
                    vec![]
                };

                args.iter()
                    .flat_map(|ty| ty.names_with(cmp.clone()))
                    .for_each(|name| names.push(name));

                names
            }
            Ty::Fn { domain, codomain } => domain
                .iter()
                .chain(std::iter::once(codomain))
                .flat_map(|ty| ty.names_with(cmp.clone()))
                .collect(),
        }
    }
}

impl<N, V: Hash + Eq + Clone> Ty<N, V> {
    pub fn bound_vars(&self) -> HashSet<V> {
        // HACK: this is a stupid implementation that clones way too much,
        // this should be implemented with a recursive helper function that
        // takes a mutable reference to a HashSet<V>
        match self {
            Ty::Prim(_) | Ty::Exists(_) => HashSet::new(),
            Ty::Forall(var) => HashSet::from([var.clone()]),
            Ty::Tuple(tys) => tys
                .iter()
                .map(|ty| ty.bound_vars())
                .reduce(|lhs, rhs| lhs.union(&rhs).cloned().collect())
                .unwrap(),
            Ty::Named { name: _, args } => args
                .iter()
                .map(|ty| ty.bound_vars())
                .reduce(|lhs, rhs| lhs.union(&rhs).cloned().collect())
                .unwrap_or_default(),
            Ty::Fn { domain, codomain } => domain
                .iter()
                .map(|ty| ty.bound_vars())
                .fold(codomain.bound_vars(), |lhs, rhs| {
                    lhs.union(&rhs).cloned().collect()
                }),
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

impl<V> Ty<BoundResult, V> {
    /// Quick constructor for a [`Ty`] wrapping a [`TypeId`] when
    /// `N = BoundResult`.
    pub fn result_of_type_id(
        ty: TypeId,
        content: Spanned<Symbol>,
        args: Box<[Arc<Self>]>,
    ) -> Self {
        Ty::Named {
            name: Ok(Bound::Global(Name {
                content,
                id: Res::Type(ty),
            })),
            args,
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
