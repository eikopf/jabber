//! Bound ASTs derived from [unbound ASTs](`super::unbound_lowered::Ast`).

use std::collections::HashMap;

use crate::{
    env::{Res, TypeId},
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

use super::common::Qualifier;

// DECLARATIONS

#[derive(Debug, Clone)]
pub enum Type<N = Bound> {
    Alias(TypeAlias<N>),
    Adt(Adt<N>),
    Extern(ExternType),
}

#[derive(Debug, Clone)]
pub struct TypeAlias<N = Bound> {
    pub name: Name<Res>,
    pub params: Box<[LocalBinding]>,
    pub ty: Spanned<Ty<N>>,
}

#[derive(Debug, Clone)]
pub struct Adt<N = Bound> {
    pub name: Name<Res>,
    pub opacity: Option<Span>,
    pub params: Box<[LocalBinding]>,
    pub constructors: HashMap<Symbol, Spanned<TyConstr<N>>>,
}

#[derive(Debug, Clone)]
pub struct ExternType {
    pub name: Name<Res>,
    pub params: Box<[LocalBinding]>,
}

#[derive(Debug, Clone)]
pub enum Term<N = Bound> {
    Fn(Fn<N>),
    ExternFn(ExternFn<N>),
    Const(Const<N>),
}

#[derive(Debug, Clone)]
pub struct Fn<N = Bound> {
    pub name: Name<Res>,
    pub params: SpanSeq<Parameter<N>>,
    pub return_ty: Option<Spanned<Ty<N>>>,
    pub body: SpanBox<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct ExternFn<N = Bound> {
    pub name: Name<Res>,
    pub params: SpanSeq<Parameter<N>>,
    pub return_ty: Option<Spanned<Ty<N>>>,
}

#[derive(Debug, Clone)]
pub struct Const<N = Bound> {
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

#[derive(Debug, Clone)]
pub enum TyConstrPayload<N = Bound> {
    Tuple(SpanSeq<Ty<N>>),
    Record(HashMap<Symbol, Spanned<RecordField<N>>>),
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

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr<N = Bound> {
    Name(N),
    Literal(LiteralExpr),
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Block(Block<N>),
    UnitConstr {
        ty: TypeId,
        name: Spanned<N>,
    },
    TupleConstr {
        ty: TypeId,
        name: Spanned<N>,
        args: SpanSeq<Self>,
    },
    RecordConstr {
        ty: TypeId,
        name: Spanned<N>,
        fields: SpanSeq<RecordExprField<N>>,
        base: Option<SpanBox<Self>>,
    },
    RecordField {
        item: SpanBox<Self>,
        field: Spanned<N>,
    },
    TupleField {
        item: SpanBox<Self>,
        field: Spanned<Symbol>,
    },
    Lambda {
        params: SpanSeq<Parameter<N>>,
        body: SpanBox<Self>,
    },
    Call {
        callee: SpanBox<Self>,
        args: SpanSeq<Self>,
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

#[derive(Debug, Clone)]
pub enum LiteralExpr {
    Unit,
    Bool(bool),
    Char(char),
    String(Symbol),
    Int(i64),
    Float(f64),
}

#[derive(Debug, Clone)]
pub struct RecordExprField<N = Bound> {
    pub field: Spanned<N>,
    pub value: Spanned<Expr<N>>,
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
    UnitConstr {
        ty: TypeId,
        name: Spanned<N>,
    },
    TupleConstr {
        ty: TypeId,
        name: Spanned<N>,
        elems: SpanSeq<Self>,
    },
    RecordConstr {
        ty: TypeId,
        name: Spanned<N>,
        fields: SpanSeq<RecordPatternField<N>>,
        rest: Option<Span>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordPatternField<N = Bound> {
    pub field: Spanned<N>,
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

    pub fn id(&self) -> BindingId {
        match self {
            Bound::Local(Name { id, .. }) => BindingId::Local(*id),
            Bound::Global(Name { id, .. }) => BindingId::Global(*id),
            Bound::Path(Name { id, .. }) => BindingId::Global(*id),
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

    pub fn as_local(&self) -> Option<Uid> {
        if let Self::Local(v) = self {
            Some(*v)
        } else {
            None
        }
    }
}

pub type LocalBinding = Name<Uid>;
pub type GlobalBinding = Name<Res>;
pub type PathBinding = Name<Res, Path>;

#[derive(Debug, Clone)]
pub struct Name<I, C = Symbol> {
    pub content: Spanned<C>,
    pub id: I,
}
