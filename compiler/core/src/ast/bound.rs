//! Bound ASTs derived from [unbound ASTs](`super::unbound_lowered::Ast`).

use crate::{
    env,
    span::{Span, SpanBox, SpanSeq, Spanned},
    symbol::Symbol,
    unique::Uid,
};

// DECLARATIONS

#[derive(Debug, Clone)]
pub enum Type {
    Alias(TypeAlias),
    Adt(Adt),
    Extern(ExternType),
}

#[derive(Debug, Clone)]
pub struct TypeAlias {
    pub name: Spanned<Ident>,
    pub params: SpanSeq<Ident>,
    pub ty: Spanned<Ty>,
}

#[derive(Debug, Clone)]
pub struct Adt {
    pub name: Spanned<Ident>,
    pub opacity: Option<Span>,
    pub params: SpanSeq<Ident>,
    pub constructors: SpanSeq<TyConstr>,
}

#[derive(Debug, Clone)]
pub struct ExternType {
    pub name: Spanned<Ident>,
    pub params: SpanSeq<Ident>,
}

#[derive(Debug, Clone)]
pub enum Term {
    Fn(Fn),
    ExternFn(ExternFn),
    Const(Const),
}

#[derive(Debug, Clone)]
pub struct Fn {
    pub name: Spanned<Ident>,
    pub params: SpanSeq<Parameter>,
    pub return_ty: Spanned<Ty>,
    pub body: SpanBox<Expr>,
}

#[derive(Debug, Clone)]
pub struct ExternFn {
    pub name: Spanned<Ident>,
    pub params: SpanSeq<Parameter>,
    pub return_ty: Spanned<Ty>,
}

#[derive(Debug, Clone)]
pub struct Const {
    pub name: Spanned<Ident>,
    pub ty: Spanned<Ty>,
    pub value: Spanned<Expr>,
}

#[derive(Debug, Clone)]
pub struct TyConstr {
    pub name: Spanned<Ident>,
    pub ty: Uid,
    pub payload: Spanned<TyConstrPayload>,
}

#[derive(Debug, Clone)]
pub enum TyConstrPayload {
    Unit,
    Tuple(SpanSeq<Ty>),
    Record(SpanSeq<RecordField>),
}

#[derive(Debug, Clone)]
pub struct RecordField {
    pub mutability: Option<Span>,
    pub name: Spanned<Ident>,
    pub ty: Spanned<Ty>,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub pattern: Spanned<Pattern>,
    pub ty: Option<Spanned<Ty>>,
}

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr {
    Term(env::TermId),
    Ident(Ident),
    Literal(LiteralExpr),
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Block(Block),
    UnitConstr {
        ty: env::TypeId,
        name: Spanned<Ident>,
    },
    TupleConstr {
        ty: env::TypeId,
        name: Spanned<Ident>,
        args: SpanSeq<Self>,
    },
    RecordConstr {
        ty: env::TypeId,
        name: Spanned<Ident>,
        fields: SpanSeq<RecordExprField>,
        base: Option<SpanBox<Self>>,
    },
    RecordField {
        item: SpanBox<Self>,
        field: Spanned<Ident>,
    },
    TupleField {
        item: SpanBox<Self>,
        field: Spanned<Symbol>,
    },
    Lambda {
        params: SpanSeq<Parameter>,
        body: SpanBox<Self>,
    },
    Call {
        callee: SpanBox<Self>,
        args: SpanSeq<Self>,
    },
    Match {
        scrutinee: SpanBox<Self>,
        arms: SpanSeq<MatchArm>,
    },
    IfElse {
        condition: SpanBox<Self>,
        consequence: SpanBox<Block>,
        alternative: SpanBox<Block>,
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
pub struct RecordExprField {
    pub field: Spanned<Ident>,
    pub value: Spanned<Expr>,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Spanned<Pattern>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub statements: SpanSeq<Stmt>,
    pub return_expr: Option<SpanBox<Expr>>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Empty,
    Expr(Expr),
    Let {
        pattern: Spanned<Pattern>,
        ty: Option<Spanned<Ty>>,
        value: Spanned<Expr>,
    },
}

// PATTERNS

#[derive(Debug, Clone)]
pub enum Pattern {
    Wildcard,
    Var(Ident),
    Literal(LiteralExpr),
    Tuple(SpanSeq<Self>),
    List(SpanSeq<Self>),
    Cons {
        head: SpanBox<Self>,
        tail: SpanBox<Self>,
    },
    UnitConstr {
        ty: env::TypeId,
        name: Spanned<Ident>,
    },
    TupleConstr {
        ty: env::TypeId,
        name: Spanned<Ident>,
        elems: SpanSeq<Self>,
    },
    RecordConstr {
        ty: env::TypeId,
        name: Spanned<Ident>,
        fields: SpanSeq<RecordPatternField>,
        rest: Option<Span>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordPatternField {
    pub field: Spanned<Ident>,
    pub pattern: Spanned<Pattern>,
}

// TYPES

#[derive(Debug, Clone)]
pub enum Ty {
    Infer,
    Never,
    Unit,
    Char,
    String,
    Int,
    Float,
    Var(Ident),
    Adt {
        name: Spanned<env::TypeId>,
        args: SpanSeq<Self>,
    },
    Fn {
        domain: SpanSeq<Self>,
        codomain: SpanBox<Self>,
    },
}

// NAMES

#[derive(Debug, Clone, Copy)]
pub struct Ident {
    pub symbol: Symbol,
    pub id: Uid,
}
