//! Concrete syntax trees and related functionality.

use crate::span::{Span, SpanBox, SpanSeq, Spanned};

/// A concrete syntax tree, which consists of an optional shebang line and a
/// list of [declarations](`Decl`).
#[derive(Debug, Clone)]
struct Cst {
    pub shebang: Option<Span>,
    pub decls: Box<[Decl]>,
}

// DECLARATIONS

#[derive(Debug, Clone)]
struct Decl {
    pub visibility: Visibility,
    pub body: Spanned<DeclBody>,
}

#[derive(Debug, Clone, Copy, Default)]
enum Visibility {
    Pub(Span),
    #[default]
    Private,
}

#[derive(Debug, Clone)]
enum DeclBody {
    Mod {
        name: Ident,
    },
    Use {
        item: UseItem,
    },
    Type {
        name: Ident,
        params: GenericParams,
        value: Type,
    },
    ExternType {
        name: Ident,
        params: GenericParams,
    },
    Struct {
        name: Ident,
        params: GenericParams,
        fields: Spanned<Box<[Spanned<StructField>]>>,
    },
    Enum {
        name: Ident,
        params: GenericParams,
        variants: Spanned<Box<[Spanned<EnumVariant>]>>,
    },
    Fn {
        name: Ident,
        params: Parameters,
        ret_ty: Option<Type>,
        body: Spanned<FnBody>,
    },
    ExternFn {
        name: Ident,
        params: Parameters,
        ret_ty: Option<Type>,
    },
    Const {
        name: Ident,
        ty: Type,
        value: Expr,
    },
}

#[derive(Debug, Clone)]
enum UseItem {
    Name(Name),
    Glob(Name),
    Alias { item: Name, alias: Ident },
    Tree { root: Name, items: Box<[Self]> },
}

#[derive(Debug, Clone)]
enum TypeAlias {
    Ident(Ident),
    Generic {
        name: Ident,
        params: Spanned<Box<[Ident]>>,
    },
}

#[derive(Debug, Clone)]
struct StructField {
    visibility: Visibility,
    mutability: Mutability,
    name: Ident,
    ty: Type,
}

#[derive(Debug, Clone, Copy, Default)]
enum Mutability {
    Mutable(Span),
    #[default]
    Immutable,
}

#[derive(Debug, Clone)]
struct EnumVariant {
    name: Ident,
    payload: Spanned<Box<[Type]>>,
}

type GenericParams = Option<Spanned<Box<[Ident]>>>;

type Parameters = Spanned<Box<[Spanned<Parameter>]>>;

#[derive(Debug, Clone)]
struct Parameter {
    pattern: Pattern,
    ty: Type,
}

#[derive(Debug, Clone)]
enum FnBody {
    EqExpr(Expr),
    Block(Block),
}

// EXPRESSIONS

type SpExpr = Spanned<Expr>;

#[derive(Debug, Clone)]
enum Expr {
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
}

#[derive(Debug, Clone, Copy)]
enum LiteralExpr {
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
struct StructExprField {
    pub name: Ident,
    pub value: Box<Expr>,
}

#[derive(Debug, Clone, Copy)]
enum FieldKind {
    Ident,
    Tuple,
}

#[derive(Debug, Clone)]
enum LambdaParams {
    Ident(Ident),
    Parameters(Parameters),
}

#[derive(Debug, Clone, Copy)]
enum PrefixOp {
    Bang,
    Star,
    Minus,
    MinusDot,
}

#[derive(Debug, Clone, Copy)]
enum BinaryOp {
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
struct MatchArm {
    pub pattern: Spanned<Pattern>,
    pub guard: Option<Spanned<Expr>>,
    pub body: Spanned<Expr>,
}

#[derive(Debug, Clone)]
struct Block {
    pub stmts: SpanSeq<Stmt>,
    pub ret_expr: Option<Spanned<Expr>>,
}

#[derive(Debug, Clone)]
enum Stmt {
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
enum Pattern {
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
}

#[derive(Debug, Clone)]
struct StructPatternField {
    pub field: Ident,
    pub pattern: Option<SpanBox<Pattern>>,
}

// TYPES

#[derive(Debug, Clone)]
enum Type {
    Inferred,
    Name(Name),
    Prim(Spanned<PrimType>),
    Paren(SpanBox<Type>),
    Tuple(SpanSeq<Type>),
    Fn(FnTypeArgs, SpanBox<Type>),
    Generic { name: Name, args: SpanSeq<Type> },
}

#[derive(Debug, Clone)]
enum FnTypeArgs {
    Simple(SpanBox<Type>),
    Parens(SpanSeq<Type>),
}

#[derive(Debug, Clone)]
enum PrimType {
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
enum Name {
    Path(SpanSeq<Ident>),
    Ident(Ident),
}

#[derive(Debug, Clone, Copy)]
struct Ident(Span);
