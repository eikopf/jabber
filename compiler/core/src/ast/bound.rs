//! Bound ASTs derived from [unbound ASTs](`super::unbound::Ast`).

use ecow::EcoString;

use crate::{
    env,
    span::{Span, SpanBox, SpanSeq, Spanned},
};

// DECLARATIONS

#[derive(Debug, Clone)]
pub enum Decl {
    TyAlias {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
        ty: Spanned<Ty>,
    },
    Ty {
        name: Spanned<Ident>,
        opacity: Option<Span>,
        params: SpanSeq<Ident>,
        constructors: SpanSeq<TyConstr>,
    },
    ExternTy {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
    },
    Fn {
        name: Spanned<Ident>,
        params: SpanSeq<Parameter>,
        return_ty: Spanned<Ty>,
        body: SpanBox<Expr>,
    },
    ExternFn {
        name: Spanned<Ident>,
        params: SpanSeq<Parameter>,
        return_ty: Spanned<Ty>,
    },
    Const {
        name: Spanned<Ident>,
        ty: Spanned<Ty>,
        value: Spanned<Expr>,
    },
}

#[derive(Debug, Clone)]
pub struct TyConstr {
    pub name: Spanned<Ident>,
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
    Decl(env::DeclId),
    Ident(Ident),
    Literal(LiteralExpr),
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Block(Block),
    Record {
        name: Spanned<env::DeclId>,
        fields: SpanSeq<RecordExprField>,
        base: Option<SpanBox<Self>>,
    },
    RecordField {
        item: SpanBox<Self>,
        field: Spanned<Ident>,
    },
    TupleField {
        item: SpanBox<Self>,
        field: Spanned<u32>,
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
    Char(char),
    String(EcoString),
    Int(i64),
    Float(f64),
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
    UnitConstr(env::DeclId),
    TupleConstr {
        name: Spanned<env::DeclId>,
        elems: SpanSeq<Self>,
    },
    RecordConstr {
        name: Spanned<env::DeclId>,
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
        name: Spanned<env::DeclId>,
        args: SpanSeq<Self>,
    },
    Fn {
        domain: SpanSeq<Self>,
        codomain: SpanBox<Self>,
    },
}

// NAMES

#[derive(Debug, Clone)]
pub struct Ident(pub EcoString);
