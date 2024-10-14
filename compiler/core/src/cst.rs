//! Concrete syntax trees and related functionality.

use crate::span::{Span, SpanBox, SpanSeq, Spanned};

/// A concrete syntax tree, which consists of an optional shebang line and a
/// list of [declarations](`Decl`).
#[derive(Debug, Clone)]
pub struct Cst {
    pub shebang: Option<Span>,
    pub decls: Box<[Decl]>,
    pub comments: Box<[Span]>,
}

// DECLARATIONS

#[derive(Debug, Clone)]
pub struct Decl {
    pub doc_comment: Option<Span>,
    pub attributes: Option<Box<[Spanned<Attr>]>>,
    pub visibility: Visibility,
    pub body: Spanned<DeclBody>,
}

#[derive(Debug, Clone, Copy, Default)]
pub enum Visibility {
    Pub(Span),
    #[default]
    Private,
}

#[derive(Debug, Clone)]
pub enum DeclBody {
    Mod {
        name: Ident,
    },
    Use {
        item: Spanned<UseItem>,
    },
    Type {
        name: Ident,
        params: GenericParams,
        value: Spanned<Type>,
    },
    ExternType {
        name: Ident,
        params: GenericParams,
    },
    Struct {
        name: Ident,
        params: GenericParams,
        fields: SpanSeq<StructField>,
    },
    Enum {
        name: Ident,
        params: GenericParams,
        variants: SpanSeq<EnumVariant>,
    },
    Fn {
        name: Ident,
        params: SpanSeq<Parameter>,
        ret_ty: Option<Spanned<Type>>,
        body: Spanned<FnBody>,
    },
    ExternFn {
        name: Ident,
        params: SpanSeq<Parameter>,
        ret_ty: Option<Spanned<Type>>,
    },
    Const {
        name: Ident,
        ty: Spanned<Type>,
        value: Spanned<Expr>,
    },
}

#[derive(Debug, Clone)]
pub enum UseItem {
    Name(Name),
    Glob(Name),
    Alias { item: Name, alias: Ident },
    Tree { root: Name, items: SpanSeq<Self> },
}

#[derive(Debug, Clone)]
pub enum TypeAlias {
    Ident(Ident),
    Generic {
        name: Ident,
        params: Spanned<Box<[Ident]>>,
    },
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub doc_comment: Option<Span>,
    pub attributes: Option<Box<[Spanned<Attr>]>>,
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub name: Ident,
    pub ty: Spanned<Type>,
}

#[derive(Debug, Clone, Copy, Default)]
pub enum Mutability {
    Mutable(Span),
    #[default]
    Immutable,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub doc_comment: Option<Span>,
    pub attributes: Option<Box<[Spanned<Attr>]>>,
    pub name: Ident,
    pub payload: SpanSeq<Type>,
}

pub type GenericParams = Option<Spanned<Box<[Ident]>>>;

#[derive(Debug, Clone)]
pub struct Parameter {
    pub pattern: Spanned<Pattern>,
    pub ty: Spanned<Type>,
}

#[derive(Debug, Clone)]
pub enum FnBody {
    EqExpr(Spanned<Expr>),
    Block(Spanned<Block>),
}

// ATTRIBUTES

#[derive(Debug, Clone)]
pub enum Attr {
    Name(Name),
    Fn { name: Name, args: SpanSeq<AttrArg> },
}

#[derive(Debug, Clone)]
pub enum AttrArg {
    Name(Name),
    Literal(Spanned<LiteralExpr>),
}

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr {
    Name(Name),
    Literal(Spanned<LiteralExpr>),
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Struct {
        name: Name,
        fields: SpanSeq<StructExprField>,
        base: Option<SpanBox<Self>>,
    },
    Field {
        item: SpanBox<Self>,
        field: Spanned<FieldKind>,
    },
    Lambda {
        params: Spanned<LambdaParams>,
        body: SpanBox<Self>,
    },
    Call {
        callee: SpanBox<Self>,
        arguments: SpanSeq<Self>,
    },
    Prefix {
        operator: Spanned<PrefixOp>,
        operand: SpanBox<Self>,
    },
    Binary {
        lhs: SpanBox<Self>,
        operator: Spanned<BinaryOp>,
        rhs: SpanBox<Self>,
    },
    Match {
        scrutinee: SpanBox<Expr>,
        arms: SpanSeq<MatchArm>,
    },
    IfElse {
        condition: SpanBox<Self>,
        consequence: SpanBox<Block>,
        alternative: Option<SpanBox<Block>>,
    },
    Block(SpanBox<Block>),
    Paren(SpanBox<Self>),
    Error(Span),
}

#[derive(Debug, Clone, Copy)]
pub enum LiteralExpr {
    Unit,
    BoolTrue,
    BoolFalse,
    Char,
    String,
    Float,
    Bin,
    Oct,
    Dec,
    Hex,
}

#[derive(Debug, Clone)]
pub struct StructExprField {
    pub name: Ident,
    pub value: SpanBox<Expr>,
}

#[derive(Debug, Clone, Copy)]
pub enum FieldKind {
    Ident,
    Tuple,
}

#[derive(Debug, Clone)]
pub enum LambdaParams {
    Ident(Ident),
    Parameters(SpanSeq<Parameter>),
}

#[derive(Debug, Clone, Copy)]
pub enum PrefixOp {
    Bang,
    Star,
    Minus,
    MinusDot,
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryOp {
    Carat,
    CaratDot,
    PipeLeft,
    PipeRight,
    EqEq,
    BangEq,
    Gt,
    GtDot,
    Lt,
    LtDot,
    Geq,
    GeqDot,
    Leq,
    LeqDot,
    Plus,
    PlusDot,
    Minus,
    MinusDot,
    Star,
    StarDot,
    Slash,
    SlashDot,
    Percent,
    Cons,
    PlusPlus,
    AmpAmp,
    BarBar,
    Walrus,
    LeftArrow,
}

#[derive(Debug, Clone)]
pub struct MatchArm {
    pub pattern: Spanned<Pattern>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
}

#[derive(Debug, Clone)]
pub struct Block {
    pub stmts: SpanSeq<Stmt>,
    pub ret_expr: Option<Spanned<Expr>>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Empty,
    Expr(Spanned<Expr>),
    Let {
        pattern: Spanned<Pattern>,
        ty: Option<Spanned<Type>>,
        value: Spanned<Expr>,
    },
}

// PATTERNS

#[derive(Debug, Clone)]
pub enum Pattern {
    Name(Name),
    Literal(Spanned<LiteralExpr>),
    Wildcard,
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Cons {
        head: SpanBox<Self>,
        tail: SpanBox<Self>,
    },
    Enum {
        name: Name,
        payload: SpanSeq<Self>,
    },
    Struct {
        name: Name,
        fields: SpanSeq<StructPatternField>,
        rest: Span,
    },
    Paren(SpanBox<Self>),
    Error(Span),
}

#[derive(Debug, Clone)]
pub struct StructPatternField {
    pub field: Ident,
    pub pattern: Option<SpanBox<Pattern>>,
}

// TYPES

#[derive(Debug, Clone)]
pub enum Type {
    Inferred,
    Name(Name),
    Prim(Spanned<PrimType>),
    Paren(SpanBox<Type>),
    Tuple(SpanSeq<Type>),
    Fn {
        domain: FnTypeArgs,
        codomain: SpanBox<Type>,
    },
    Generic {
        name: Name,
        args: SpanSeq<Type>,
    },
    Error(Span),
}

#[derive(Debug, Clone)]
pub enum FnTypeArgs {
    NoParens(SpanBox<Type>),
    Parens(SpanSeq<Type>),
}

#[derive(Debug, Clone)]
pub enum PrimType {
    Never,
    Unit,
    Bool,
    Char,
    String,
    Int,
    Float,
}

// NAMES

#[derive(Debug, Clone)]
pub enum Name {
    Path(SpanSeq<Ident>),
    Ident(Ident),
}

#[derive(Debug, Clone, Copy)]
pub struct Ident(pub Span);
