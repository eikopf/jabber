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
    Name, NameContent, Path, PathBinding, ResAttr, Ty as TyAst,
    TyConstr as TyConstrAst,
};

// DECLARATIONS

/// A type declaration.
///
/// Based on the value of `kind`, this struct will represent either an ADT,
/// a type alias, or an external type declaration.
#[derive(Debug, Clone)]
pub struct Type<V = Uid, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub params: Box<[LocalBinding]>,
    pub kind: TypeKind<V>,
}

impl<V, A> Type<V, A> {
    pub fn constrs(&self) -> Option<&HashMap<Symbol, Spanned<TyConstr<V>>>> {
        match &self.kind {
            TypeKind::Adt { constrs, .. } => Some(constrs),
            _ => None,
        }
    }

    pub fn as_struct_constr(&self) -> Option<&TyConstr<V>> {
        match &self.kind {
            TypeKind::Adt {
                opacity: None,
                constrs,
            } if constrs.len() == 1 => {
                constrs.get(&self.name.content).map(Spanned::item)
            }
            _ => None,
        }
    }
}

/// The kind of a [`Type`] together with any specific elements belonging to
/// each kind.
#[derive(Debug, Clone)]
pub enum TypeKind<V = Uid> {
    Alias {
        rhs_ast: Spanned<TyAst<BoundResult>>,
        rhs_ty: Arc<Ty<V>>,
    },
    Adt {
        opacity: Option<Span>,
        constrs: HashMap<Symbol, Spanned<TyConstr<V>>>,
    },
    Extern,
}

#[derive(Debug, Clone)]
pub struct TyConstr<V = Uid> {
    pub name: Spanned<Symbol>,
    pub ast: Spanned<TyConstrAst<BoundResult>>,
    pub kind: TyConstrKind<V>,
}

impl<V> TyConstr<V> {
    pub fn get_ty(&self) -> Option<&Arc<Ty<V>>> {
        match &self.kind {
            TyConstrKind::Record(_) => None,
            TyConstrKind::Unit(ty) => Some(ty),
            TyConstrKind::Tuple { fn_ty, .. } => Some(fn_ty),
        }
    }

    pub fn is_tuple(&self) -> bool {
        self.kind.is_tuple()
    }

    pub fn is_record(&self) -> bool {
        self.kind.is_record()
    }

    pub fn is_unit(&self) -> bool {
        self.kind.is_unit()
    }
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
pub enum TyConstrKind<V = Uid> {
    /// A constant constructor.
    Unit(Arc<Ty<V>>),
    /// A record constructor.
    Record(HashMap<Symbol, RecordField<V>>),
    /// A tuple constructor.
    Tuple {
        /// The element types of the constructor.
        elems: Box<[Arc<Ty<V>>]>,
        /// The type of the constructor as a function. This is the type of the
        /// constructor when it is referred to by name, e.g. in a call expr.
        fn_ty: Arc<Ty<V>>,
    },
}

impl<V> TyConstrKind<V> {
    /// Returns `true` if the ty constr kind is [`Tuple`].
    ///
    /// [`Tuple`]: TyConstrKind::Tuple
    #[must_use]
    pub fn is_tuple(&self) -> bool {
        matches!(self, Self::Tuple { .. })
    }

    /// Returns `true` if the ty constr kind is [`Record`].
    ///
    /// [`Record`]: TyConstrKind::Record
    #[must_use]
    pub fn is_record(&self) -> bool {
        matches!(self, Self::Record(..))
    }

    /// Returns `true` if the ty constr kind is [`Unit`].
    ///
    /// [`Unit`]: TyConstrKind::Unit
    #[must_use]
    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Unit(..))
    }
}

#[derive(Debug, Clone)]
pub struct RecordField<V = Uid> {
    pub mutability: Option<Span>,
    pub name: Spanned<Symbol>,
    pub ty: Arc<Ty<V>>,
}

#[derive(Debug, Clone)]
pub struct Term<V = Uid, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub ty: Arc<Ty<V>>,
    pub kind: TermKind<V>,
}

#[derive(Debug, Clone)]
pub enum TermKind<V = Uid> {
    Fn {
        params: SpanSeq<Parameter<V>>,
        return_ty_ast: Option<Spanned<TyAst<BoundResult>>>,
        body: Spanned<Typed<Expr<V>, V>>,
    },
    ExternFn {
        params: SpanSeq<Parameter<V>>,
        return_ty_ast: Option<Spanned<TyAst<BoundResult>>>,
    },
    Const {
        ty_ast: Option<Spanned<TyAst<BoundResult>>>,
        value: Spanned<Typed<Expr<V>, V>>,
    },
}

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr<V = Uid> {
    /// A local variable.
    Local(Name<Uid>),
    /// A name (ident or path) bound to a [`Res`].
    Global(Name<Res, NameContent>),
    Literal(LiteralExpr),
    List(TySpanSeq<Self, V>),
    Tuple(TySpanSeq<Self, V>),
    Block {
        statements: SpanSeq<Stmt<V>>,
        return_expr: Option<TySpanBox<Self, V>>,
    },
    RecordConstr {
        name: Bound,
        fields: SpanSeq<RecordExprField<V>>,
        base: Option<TySpanBox<Self, V>>,
    },
    RecordField {
        item: TySpanBox<Self, V>,
        field: Spanned<Symbol>,
    },
    TupleField {
        item: TySpanBox<Self, V>,
        field: Spanned<Option<u32>>,
    },
    Lambda {
        params: SpanSeq<Parameter<V>>,
        body: TySpanBox<Self, V>,
    },
    Call {
        callee: TySpanBox<Self, V>,
        args: TySpanSeq<Self, V>,
        kind: CallExprKind,
    },
    Lazy {
        operator: Spanned<LazyOperator>,
        lhs: TySpanBox<Self, V>,
        rhs: TySpanBox<Self, V>,
    },
    Mutate {
        operator: Span,
        item: TySpanBox<Self, V>,
        field: Spanned<Symbol>,
        rhs: TySpanBox<Self, V>,
    },
    Match {
        scrutinee: TySpanBox<Self, V>,
        arms: SpanSeq<MatchArm<V>>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordExprField<V = Uid> {
    pub field: Spanned<Symbol>,
    pub value: Spanned<Typed<Expr<V>, V>>,
}

#[derive(Debug, Clone)]
pub enum Stmt<V = Uid> {
    Expr(Typed<Expr<V>, V>),
    Let {
        pattern: Spanned<Pattern<V>>,
        value: Spanned<Typed<Expr<V>, V>>,
    },
}

/// A lazy logical operator.
#[derive(Debug, Clone, Copy)]
pub enum LazyOperator {
    And,
    Or,
}

#[derive(Debug, Clone)]
pub struct MatchArm<V = Uid> {
    pub pattern: Spanned<Pattern<V>>,
    pub body: Spanned<Typed<Expr<V>, V>>,
}

// PATTERNS

#[derive(Debug, Clone)]
pub struct Parameter<V = Uid> {
    pub pattern: Spanned<Pattern<V>>,
    pub ty: Arc<Ty<V>>,
    pub ty_ast: Option<Spanned<TyAst<BoundResult>>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyConstrIndex {
    pub ty: TypeId,
    pub name: Symbol,
}

#[derive(Debug, Clone)]
pub enum Pattern<V> {
    Wildcard,
    Literal(LiteralExpr),
    Var(Typed<Name<Uid>, V>),
    Tuple(SpanSeq<Self>),
    List(SpanSeq<Self>),
    Cons {
        head: SpanBox<Self>,
        tail: SpanBox<Self>,
    },
    UnitConstr {
        name: Name<TyConstrIndex, Bound>,
    },
    TupleConstr {
        name: Name<TyConstrIndex, Bound>,
        elems: SpanSeq<Self>,
    },
    RecordConstr {
        name: Name<TyConstrIndex, Bound>,
        fields: SpanSeq<FieldPattern<V>>,
        rest: Option<Span>,
    },
}

impl<V> Pattern<V> {
    pub fn is_unit(&self) -> bool {
        matches!(self, Pattern::Literal(LiteralExpr::Unit))
    }
}

#[derive(Debug, Clone)]
pub struct FieldPattern<V> {
    pub name: Symbol,
    pub pattern: Spanned<Pattern<V>>,
}

// PROPER TYPES

pub type TySpanSeq<T, V> = SpanSeq<Typed<T, V>>;
pub type TySpanBox<T, V> = SpanBox<Typed<T, V>>;
pub type TyBox<T, V> = Box<Typed<T, V>>;

#[derive(Debug, Clone)]
pub struct Typed<T, V = Uid> {
    pub item: T,
    pub ty: Arc<Ty<V>>,
}

impl<T, V> Typed<T, V> {
    pub fn as_ref(&self) -> Typed<&T, V> {
        Typed {
            item: &self.item,
            ty: self.ty.clone(), // this is bad design!
        }
    }
}

impl<T, V> std::ops::Deref for Typed<T, V> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.item
    }
}

#[derive(Debug, Clone)]
pub struct Ty<V = Uid> {
    pub prefix: HashSet<V>,
    pub matrix: Arc<TyMatrix<V>>,
}

/// A type with names of type `N` and variables of type `V`. Recursive variants
/// are stored with [`Arc`] so cloning can be cheap during unification.
#[derive(Debug, Clone)]
pub enum TyMatrix<V = Uid> {
    /// A primitive type.
    Prim(PrimTy),
    /// An existentially-quantified type.
    Var(V),
    /// A product of at least two types.
    Tuple(Box<[Arc<Self>]>),
    /// A named type with 0 or more arguments.
    Named {
        name: TypeId,
        args: Box<[Arc<Self>]>,
    },
    /// A function type with a domain of arbitrary arity.
    Fn {
        domain: Box<[Arc<Self>]>,
        codomain: Arc<Self>,
    },
}

impl<V> Ty<V> {
    /// Annotates an item with `self`.
    pub fn with<T>(self: &Arc<Self>, item: T) -> Typed<T, V> {
        Typed {
            item,
            ty: self.clone(),
        }
    }

    pub fn bound_vars(&self) -> &HashSet<V> {
        &self.prefix
    }

    pub fn prim(matrix: PrimTy) -> Self {
        Self {
            matrix: Arc::new(TyMatrix::Prim(matrix)),
            prefix: Default::default(),
        }
    }

    pub fn unquantified(matrix: Arc<TyMatrix<V>>) -> Arc<Self> {
        Arc::new(Self {
            prefix: Default::default(),
            matrix,
        })
    }

    pub fn is_unquantified(&self) -> bool {
        self.prefix.is_empty()
    }

    /// Returns the names in `self` for which `cmp` returns `true`.
    pub fn names_with<F>(&self, cmp: F) -> Vec<TypeId>
    where
        F: Fn(&TypeId) -> bool + Clone,
    {
        self.matrix.names_with(cmp)
    }
}

impl<V: Hash + Eq + Clone> Ty<V> {
    /// Returns `true` if and only if `self` does not contain unquantified
    /// type variables.
    pub fn is_concrete(&self) -> bool {
        fn rec<V: Hash + Eq + Clone>(
            prefix: &HashSet<V>,
            matrix: &TyMatrix<V>,
        ) -> bool {
            match matrix {
                TyMatrix::Prim(_) => true,
                TyMatrix::Var(var) => prefix.contains(var),
                TyMatrix::Tuple(elems) => {
                    elems.iter().all(|elem| rec(prefix, elem))
                }
                TyMatrix::Named { name: _, args } => {
                    args.iter().all(|arg| rec(prefix, arg))
                }
                TyMatrix::Fn { domain, codomain } => {
                    domain.iter().all(|elem| rec(prefix, elem))
                        && rec(prefix, codomain)
                }
            }
        }

        rec(&self.prefix, &self.matrix)
    }
}

impl Ty<Uid> {
    pub fn fresh_unbound() -> Self {
        let matrix = Arc::new(TyMatrix::fresh_var());

        Self {
            prefix: Default::default(),
            matrix,
        }
    }

    pub fn fresh_unbound_tuple(len: usize) -> Self {
        let mut elems = Vec::with_capacity(len);

        for _ in 0..len {
            let elem = Arc::new(TyMatrix::fresh_var());
            elems.push(elem);
        }

        let matrix = Arc::new(TyMatrix::Tuple(elems.into_boxed_slice()));

        Self {
            prefix: Default::default(),
            matrix,
        }
    }

    pub fn fresh_unbound_fn(arity: usize) -> Self {
        let mut domain = Vec::with_capacity(arity);

        for _ in 0..arity {
            let elem = Arc::new(TyMatrix::fresh_var());
            domain.push(elem);
        }

        let matrix = Arc::new(TyMatrix::Fn {
            domain: domain.into_boxed_slice(),
            codomain: Arc::new(TyMatrix::fresh_var()),
        });

        Self {
            prefix: Default::default(),
            matrix,
        }
    }
}

impl<V> TyMatrix<V> {
    /// Returns the names in `self` for which `cmp` returns `true`.
    pub fn names_with<F>(&self, cmp: F) -> Vec<TypeId>
    where
        F: Fn(&TypeId) -> bool + Clone,
    {
        match self {
            TyMatrix::Prim(_) | TyMatrix::Var(_) => vec![],
            TyMatrix::Tuple(elems) => elems
                .iter()
                .flat_map(|elem| elem.names_with(cmp.clone()))
                .collect(),
            TyMatrix::Named { name, args } => {
                let mut names = vec![];

                if cmp(name) {
                    names.push(*name);
                }

                let tail =
                    args.iter().flat_map(|arg| arg.names_with(cmp.clone()));

                names.extend(tail);
                names
            }
            TyMatrix::Fn { domain, codomain } => {
                let mut names: Vec<_> = domain
                    .iter()
                    .flat_map(|elem| elem.names_with(cmp.clone()))
                    .collect();
                names.extend(codomain.names_with(cmp.clone()));
                names
            }
        }
    }

    pub fn vars(&self) -> HashSet<V>
    where
        V: Clone + Eq + Hash,
    {
        fn rec<V: Clone + Eq + Hash>(
            matrix: &TyMatrix<V>,
            vars: &mut HashSet<V>,
        ) {
            match matrix {
                TyMatrix::Prim(_) => (),
                TyMatrix::Var(var) => {
                    vars.insert(var.clone());
                }
                TyMatrix::Tuple(elems) => {
                    elems.iter().for_each(|ty| rec(ty, vars))
                }
                TyMatrix::Named { name: _, args } => {
                    args.iter().for_each(|ty| rec(ty, vars))
                }
                TyMatrix::Fn { domain, codomain } => {
                    domain.iter().for_each(|ty| rec(ty, vars));
                    rec(codomain, vars)
                }
            }
        }

        let mut vars = HashSet::new();
        rec(self, &mut vars);
        vars
    }

    pub fn as_fn(self: &Arc<Self>) -> Option<(Domain<V>, Arc<Self>)> {
        match self.as_ref() {
            TyMatrix::Fn { domain, codomain } => {
                Some((domain.clone(), codomain.clone()))
            }
            _ => None,
        }
    }
}

type Domain<V> = Box<[Arc<TyMatrix<V>>]>;

impl TyMatrix<Uid> {
    pub fn fresh_var() -> Self {
        Self::Var(Uid::fresh())
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
