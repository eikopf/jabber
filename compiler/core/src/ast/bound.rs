//! Bound ASTs derived from [unbound ASTs](`super::unbound_lowered::Ast`).

use std::collections::HashMap;

use crate::{
    env::{Res, TypeId},
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

use super::common::Qualifier;

pub use super::attr::{Attr, AttrArg, AttrName};

// DECLARATIONS

#[derive(Debug, Clone)]
pub enum Type<N = Bound, A = ResAttr> {
    Alias(TypeAlias<N, A>),
    Adt(Adt<N, A>),
    Extern(ExternType<A>),
}

impl<N> Type<N> {
    pub fn as_adt(&self) -> Option<&Adt<N>> {
        if let Self::Adt(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn name(&self) -> Name<Res> {
        match self {
            Type::Adt(Adt { name, .. })
            | Type::Alias(TypeAlias { name, .. })
            | Type::Extern(ExternType { name, .. }) => *name,
        }
    }
}

#[derive(Debug, Clone)]
pub struct TypeAlias<N = Bound, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub params: Box<[LocalBinding]>,
    pub ty: Spanned<Ty<N>>,
}

#[derive(Debug, Clone)]
pub struct Adt<N = Bound, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub opacity: Option<Span>,
    pub params: Box<[LocalBinding]>,
    pub constructors: HashMap<Symbol, Spanned<TyConstr<N>>>,
}

#[derive(Debug, Clone)]
pub struct ExternType<A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub params: Box<[LocalBinding]>,
}

#[derive(Debug, Clone)]
pub enum Term<N = Bound, A = ResAttr> {
    Fn(Fn<N, A>),
    ExternFn(ExternFn<N, A>),
    Const(Const<N, A>),
}

#[derive(Debug, Clone)]
pub struct Fn<N = Bound, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub params: SpanSeq<Parameter<N>>,
    pub return_ty: Option<Spanned<Ty<N>>>,
    pub body: SpanBox<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct ExternFn<N = Bound, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub params: SpanSeq<Parameter<N>>,
    pub return_ty: Option<Spanned<Ty<N>>>,
}

#[derive(Debug, Clone)]
pub struct Const<N = Bound, A = ResAttr> {
    pub attrs: SpanSeq<A>,
    pub name: Name<Res>,
    pub ty: Option<Spanned<Ty<N>>>,
    pub value: Spanned<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct TyConstr<N = Bound> {
    pub name: Spanned<Symbol>,
    pub ty: TypeId,
    pub payload: Option<Spanned<TyConstrPayload<N>>>,
}

impl<N> TyConstr<N> {
    pub fn payload(&self) -> Option<&Spanned<TyConstrPayload<N>>> {
        self.payload.as_ref()
    }
}

#[derive(Debug, Clone)]
pub enum TyConstrPayload<N = Bound> {
    Tuple(SpanSeq<Ty<N>>),
    Record(HashMap<Symbol, Spanned<RecordField<N>>>),
}

impl<N> TyConstrPayload<N> {
    pub fn as_tuple(&self) -> Option<&SpanSeq<Ty<N>>> {
        if let Self::Tuple(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_record(
        &self,
    ) -> Option<&HashMap<Symbol, Spanned<RecordField<N>>>> {
        if let Self::Record(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct RecordField<N = Bound> {
    pub mutability: Option<Span>,
    pub name: Spanned<Symbol>,
    pub ty: Spanned<Ty<N>>,
}

#[derive(Debug, Clone)]
pub struct Parameter<N = Bound> {
    pub pattern: Spanned<Pattern<N>>,
    pub ty: Option<Spanned<Ty<N>>>,
}

// ATTRIBUTES

/// An attribute produced during name resolution.
pub type ResAttr = Attr<
    Result<Spanned<AttrName>, Spanned<NameContent>>,
    Result<Bound, Spanned<NameContent>>,
>;

/// A well-formed attribute.
pub type BoundAttr = Attr<Spanned<AttrName>, Bound>;

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr<N = Bound> {
    Name(N),
    Literal(LiteralExpr),
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Block(Block<N>),
    RecordConstr {
        name: N,
        fields: SpanSeq<RecordExprField<N>>,
        base: Option<SpanBox<Self>>,
    },
    RecordField {
        item: SpanBox<Self>,
        field: Spanned<Symbol>,
    },
    TupleField {
        item: SpanBox<Self>,
        /// will be `None` if the index overflowed (i.e. exceeded `u32::MAX`)
        field: Spanned<Option<u32>>,
    },
    Lambda {
        params: SpanSeq<Parameter<N>>,
        body: SpanBox<Self>,
    },
    Call {
        callee: SpanBox<Self>,
        args: SpanSeq<Self>,
        kind: CallExprKind,
    },
    LazyAnd {
        operator: Span,
        lhs: SpanBox<Self>,
        rhs: SpanBox<Self>,
    },
    LazyOr {
        operator: Span,
        lhs: SpanBox<Self>,
        rhs: SpanBox<Self>,
    },
    Mutate {
        operator: Span,
        lhs: SpanBox<Self>,
        rhs: SpanBox<Self>,
    },
    Match {
        scrutinee: SpanBox<Self>,
        arms: SpanSeq<MatchArm<N>>,
    },
    IfElse {
        condition: SpanBox<Self>,
        consequence: SpanBox<Block<N>>,
        alternative: Option<SpanBox<Block<N>>>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum LiteralExpr {
    Unit,
    Bool(bool),
    Char(char),
    String(Symbol),
    Int(u64),
    Float(f64),
    Malformed(MalformedLiteral),
}

/// The set of literal types that can be grammatically well-formed but
/// semantically ill-formed.
#[derive(Debug, Clone, Copy)]
pub enum MalformedLiteral {
    Char,
    String,
    Int,
}

#[derive(Debug, Clone)]
pub struct RecordExprField<N = Bound> {
    pub field: Spanned<Symbol>,
    pub value: Spanned<Expr<N>>,
}

#[derive(Debug, Clone, Copy)]
pub enum CallExprKind {
    Normal,
    DesugaredPrefixOp,
    DesugaredBinaryOp,
}

#[derive(Debug, Clone)]
pub struct MatchArm<N = Bound> {
    pub pattern: Spanned<Pattern<N>>,
    pub body: Spanned<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct Block<N = Bound> {
    pub statements: SpanSeq<Stmt<N>>,
    pub return_expr: Option<SpanBox<Expr<N>>>,
}

#[derive(Debug, Clone)]
pub enum Stmt<N = Bound> {
    Empty,
    Expr(Expr<N>),
    Let {
        pattern: Spanned<Pattern<N>>,
        ty: Option<Spanned<Ty<N>>>,
        value: Spanned<Expr<N>>,
    },
}

// PATTERNS

#[derive(Debug, Clone)]
pub enum Pattern<N = Bound> {
    Wildcard,
    Name(N),
    Literal(LiteralExpr),
    Tuple(SpanSeq<Self>),
    List(SpanSeq<Self>),
    Cons {
        head: SpanBox<Self>,
        tail: SpanBox<Self>,
    },
    TupleConstr {
        name: N,
        elems: SpanSeq<Self>,
    },
    RecordConstr {
        name: N,
        fields: SpanSeq<RecordPatternField<N>>,
        rest: Option<Span>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordPatternField<N = Bound> {
    pub field: Spanned<Symbol>,
    pub pattern: Spanned<Pattern<N>>,
}

// TYPES

#[derive(Debug, Clone)]
pub enum Ty<N = Bound> {
    Infer,
    Never,
    Unit,
    Bool,
    Char,
    String,
    Int,
    Float,
    Tuple(SpanSeq<Self>),
    Named {
        name: N,
        args: SpanSeq<Self>,
    },
    Fn {
        domain: Spanned<SpanSeq<Self>>,
        codomain: SpanBox<Self>,
    },
}

// NAMES

#[derive(Debug, Clone)]
pub enum Bound {
    Local(LocalBinding),
    Path(PathBinding),
    Global(GlobalBinding),
}

impl From<GlobalBinding> for Bound {
    fn from(v: GlobalBinding) -> Self {
        Self::Global(v)
    }
}

impl Bound {
    pub fn content(self) -> Spanned<NameContent> {
        match self {
            Bound::Local(Name { content, .. })
            | Bound::Global(Name { content, .. }) => {
                content.span.with(NameContent::Ident(content.item))
            }
            Bound::Path(Name {
                content: Spanned { item, span },
                ..
            }) => span.with(NameContent::Path(item)),
        }
    }

    pub fn span(&self) -> Span {
        match self {
            Bound::Local(name) => name.content.span,
            Bound::Path(name) => name.content.span,
            Bound::Global(name) => name.content.span,
        }
    }

    pub fn id(&self) -> BindingId {
        match self {
            Bound::Local(Name { id, .. }) => BindingId::Local(*id),
            Bound::Global(Name { id, .. }) => BindingId::Global(*id),
            Bound::Path(Name { id, .. }) => BindingId::Global(*id),
        }
    }

    pub fn as_local(&self) -> Option<LocalBinding> {
        if let Self::Local(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub enum NameContent {
    Ident(Symbol),
    Path(Path),
}

impl NameContent {
    pub fn as_ident(&self) -> Option<Symbol> {
        if let Self::Ident(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

impl From<Path> for NameContent {
    fn from(v: Path) -> Self {
        Self::Path(v)
    }
}

impl From<Symbol> for NameContent {
    fn from(v: Symbol) -> Self {
        Self::Ident(v)
    }
}

#[derive(Debug, Clone)]
pub struct Path {
    pub qualifier: Option<Spanned<Qualifier>>,
    pub elements: SpanSeq<Symbol>,
}

#[derive(Debug, Clone, Copy)]
pub enum BindingId {
    Local(Uid),
    Global(Res),
}

impl BindingId {
    pub fn with_ident(self, content: Spanned<Symbol>) -> Bound {
        match self {
            BindingId::Local(id) => Bound::Local(Name { content, id }),
            BindingId::Global(id) => Bound::Global(Name { content, id }),
        }
    }

    pub fn with_path(self, content: Spanned<Path>) -> Bound {
        match self {
            BindingId::Global(id) => Bound::Path(Name { content, id }),
            BindingId::Local(uid) => panic!(
                "Tried to bind the path {:?} with the local ID {:?}",
                content, uid
            ),
        }
    }

    pub fn as_local(self) -> Option<Uid> {
        if let Self::Local(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_global(self) -> Option<Res> {
        if let Self::Global(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

pub type LocalBinding = Name<Uid>;
pub type GlobalBinding = Name<Res>;
pub type PathBinding = Name<Res, Path>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Name<I, C = Symbol> {
    pub content: Spanned<C>,
    pub id: I,
}
