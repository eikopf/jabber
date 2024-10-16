//! Concrete syntax trees and related functionality.

use crate::span::{Span, SpanBox, SpanSeq, Spanned};

/// A concrete syntax tree, which consists of an optional shebang line and a
/// list of [declarations](`Decl`).
#[derive(Debug, Clone)]
pub struct Cst {
    pub shebang: Option<Span>,
    pub mod_comment: Option<Span>,
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
        name: Spanned<Ident>,
    },
    Use {
        item: Spanned<UseItem>,
    },
    Type {
        name: Spanned<Ident>,
        params: Option<SpanSeq<Ident>>,
        value: Spanned<Type>,
    },
    ExternType {
        name: Spanned<Ident>,
        params: Option<SpanSeq<Ident>>,
    },
    Struct {
        name: Spanned<Ident>,
        params: Option<SpanSeq<Ident>>,
        fields: SpanSeq<StructField>,
    },
    Enum {
        name: Spanned<Ident>,
        params: Option<SpanSeq<Ident>>,
        variants: SpanSeq<EnumVariant>,
    },
    Fn {
        name: Spanned<Ident>,
        params: SpanSeq<Parameter>,
        ret_ty: Option<Spanned<Type>>,
        body: Spanned<FnBody>,
    },
    ExternFn {
        name: Spanned<Ident>,
        params: SpanSeq<Parameter>,
        ret_ty: Option<Spanned<Type>>,
    },
    Const {
        name: Spanned<Ident>,
        ty: Spanned<Type>,
        value: Spanned<Expr>,
    },
}

#[derive(Debug, Clone)]
pub enum UseItem {
    Name(Spanned<Name>),
    Glob(Spanned<Name>),
    Alias {
        item: Spanned<Name>,
        alias: Spanned<Ident>,
    },
    Tree {
        root: Spanned<Name>,
        items: SpanSeq<Self>,
    },
}

#[derive(Debug, Clone)]
pub enum TypeAlias {
    Ident(Spanned<Ident>),
    Generic {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
    },
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub doc_comment: Option<Span>,
    pub attributes: Option<Box<[Spanned<Attr>]>>,
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub name: Spanned<Ident>,
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
    pub name: Spanned<Ident>,
    pub payload: SpanSeq<Type>,
}

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
    Name(Spanned<Name>),
    Fn {
        name: Spanned<Name>,
        args: SpanSeq<AttrArg>,
    },
}

#[derive(Debug, Clone)]
pub enum AttrArg {
    Name(Spanned<Name>),
    Literal(Spanned<LiteralExpr>),
}

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr {
    Name(Spanned<Name>),
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
    pub name: Spanned<Ident>,
    pub value: SpanBox<Expr>,
}

#[derive(Debug, Clone, Copy)]
pub enum FieldKind {
    Ident,
    Tuple,
}

#[derive(Debug, Clone)]
pub enum LambdaParams {
    Ident(Spanned<Ident>),
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
    Name(Spanned<Name>),
    Literal(Spanned<LiteralExpr>),
    Wildcard,
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Cons {
        head: SpanBox<Self>,
        tail: SpanBox<Self>,
    },
    Enum {
        name: Spanned<Name>,
        payload: SpanSeq<Self>,
    },
    Struct {
        name: Spanned<Name>,
        fields: SpanSeq<StructPatternField>,
        rest: Span,
    },
    Paren(SpanBox<Self>),
}

#[derive(Debug, Clone)]
pub struct StructPatternField {
    pub field: Spanned<Ident>,
    pub pattern: Option<SpanBox<Pattern>>,
}

// TYPES

#[derive(Debug, Clone)]
pub enum Type {
    Inferred,
    Name(Spanned<Name>),
    Prim(Spanned<PrimType>),
    Paren(SpanBox<Type>),
    Tuple(SpanSeq<Type>),
    Fn {
        domain: FnTypeArgs,
        codomain: SpanBox<Type>,
    },
    Generic {
        name: Spanned<Name>,
        args: SpanSeq<Type>,
    },
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

/// A name, which may be a path or a single identifier.
#[derive(Debug, Clone)]
pub enum Name {
    Path(Box<[Spanned<Ident>]>),
    Ident(Ident),
}

/// A ZST representing identifiers. An ident has no internal structure, so
/// a `Spanned<Ident>` is a complete description of a valid identifier
/// (assuming it has been constructed correctly).
#[derive(Debug, Clone, Copy)]
pub struct Ident;
