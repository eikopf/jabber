//! Bound ASTs derived from [unbound ASTs](`super::unbound_lowered::Ast`).

use crate::{
    env,
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

// DECLARATIONS

#[derive(Debug, Clone)]
pub enum Type<N = Name> {
    Alias(TypeAlias<N>),
    Adt(Adt<N>),
    Extern(ExternType<N>),
}

#[derive(Debug, Clone)]
pub struct TypeAlias<N = Name> {
    pub name: Spanned<N>,
    pub params: SpanSeq<N>,
    pub ty: Spanned<Ty<N>>,
}

#[derive(Debug, Clone)]
pub struct Adt<N = Name> {
    pub name: Spanned<N>,
    pub opacity: Option<Span>,
    pub params: SpanSeq<N>,
    pub constructors: SpanSeq<TyConstr<N>>,
}

#[derive(Debug, Clone)]
pub struct ExternType<N = Name> {
    pub name: Spanned<N>,
    pub params: SpanSeq<N>,
}

#[derive(Debug, Clone)]
pub enum Term<N = Name> {
    Fn(Fn<N>),
    ExternFn(ExternFn<N>),
    Const(Const<N>),
}

#[derive(Debug, Clone)]
pub struct Fn<N = Name> {
    pub name: Spanned<N>,
    pub params: SpanSeq<Parameter<N>>,
    pub return_ty: Spanned<Ty<N>>,
    pub body: SpanBox<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct ExternFn<N = Name> {
    pub name: Spanned<N>,
    pub params: SpanSeq<Parameter<N>>,
    pub return_ty: Spanned<Ty<N>>,
}

#[derive(Debug, Clone)]
pub struct Const<N = Name> {
    pub name: Spanned<N>,
    pub ty: Spanned<Ty<N>>,
    pub value: Spanned<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct TyConstr<N = Name> {
    pub name: Spanned<N>,
    pub ty: env::TypeId,
    pub payload: Spanned<TyConstrPayload<N>>,
}

#[derive(Debug, Clone)]
pub enum TyConstrPayload<N = Name> {
    Unit,
    Tuple(SpanSeq<Ty<N>>),
    Record(SpanSeq<RecordField<N>>),
}

#[derive(Debug, Clone)]
pub struct RecordField<N = Name> {
    pub mutability: Option<Span>,
    pub name: Spanned<N>,
    pub ty: Spanned<Ty<N>>,
}

#[derive(Debug, Clone)]
pub struct Parameter<N = Name> {
    pub pattern: Spanned<Pattern<N>>,
    pub ty: Option<Spanned<Ty<N>>>,
}

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr<N = Name> {
    Term(env::TermId),
    Ident(N),
    Literal(LiteralExpr),
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Block(Block<N>),
    UnitConstr {
        ty: env::TypeId,
        name: Spanned<N>,
    },
    TupleConstr {
        ty: env::TypeId,
        name: Spanned<N>,
        args: SpanSeq<Self>,
    },
    RecordConstr {
        ty: env::TypeId,
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
    Char(Symbol),
    String(Symbol),
    Int(Symbol),
    Float(Symbol),
}

#[derive(Debug, Clone)]
pub struct RecordExprField<N = Name> {
    pub field: Spanned<N>,
    pub value: Spanned<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct MatchArm<N = Name> {
    pub pattern: Spanned<Pattern<N>>,
    pub body: Spanned<Expr<N>>,
}

#[derive(Debug, Clone)]
pub struct Block<N = Name> {
    pub statements: SpanSeq<Stmt<N>>,
    pub return_expr: Option<SpanBox<Expr<N>>>,
}

#[derive(Debug, Clone)]
pub enum Stmt<N = Name> {
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
pub enum Pattern<N = Name> {
    Wildcard,
    Var(N),
    Literal(LiteralExpr),
    Tuple(SpanSeq<Self>),
    List(SpanSeq<Self>),
    Cons {
        head: SpanBox<Self>,
        tail: SpanBox<Self>,
    },
    UnitConstr {
        ty: env::TypeId,
        name: Spanned<N>,
    },
    TupleConstr {
        ty: env::TypeId,
        name: Spanned<N>,
        elems: SpanSeq<Self>,
    },
    RecordConstr {
        ty: env::TypeId,
        name: Spanned<N>,
        fields: SpanSeq<RecordPatternField<N>>,
        rest: Option<Span>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordPatternField<N = Name> {
    pub field: Spanned<N>,
    pub pattern: Spanned<Pattern<N>>,
}

// TYPES

#[derive(Debug, Clone)]
pub enum Ty<N = Name> {
    Infer,
    Never,
    Unit,
    Char,
    String,
    Int,
    Float,
    Var(N),
    Named {
        ty: env::TypeId,
        name: Spanned<Symbol>,
        args: SpanSeq<Self>,
    },
    Fn {
        domain: SpanSeq<Self>,
        codomain: SpanBox<Self>,
    },
}

// NAMES

#[derive(Debug, Clone, Copy)]
pub enum Name {
    Local {
        ident: Spanned<Symbol>,
        id: Uid,
    },
    Global {
        ident: Spanned<Symbol>,
        id: env::Res,
    },
}
