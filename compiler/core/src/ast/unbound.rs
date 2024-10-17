//! Unbound ASTs derived from CSTs

use crate::span::{Span, SpanBox, SpanSeq, Spanned};

#[derive(Debug, Clone)]
pub struct Ast {
    shebang: Option<Span>,
    module_comment: Option<Span>,
    comments: Box<[Span]>,
    decls: SpanSeq<Decl>,
}

impl Ast {
    pub fn empty() -> Self {
        Self {
            shebang: None,
            module_comment: None,
            comments: Vec::new().into_boxed_slice(),
            decls: Vec::new().into_boxed_slice(),
        }
    }
}

// DECLARATIONS

#[derive(Debug, Clone)]
pub struct Decl {
    pub doc_comment: Option<Span>,
    pub attributes: SpanSeq<Attr>,
    pub visibility: Visibility,
    pub kind: Spanned<DeclKind>,
}

#[derive(Debug, Clone, Copy, Default)]
pub enum Visibility {
    Pub(Span),
    #[default]
    Priv,
}

#[derive(Debug, Clone)]
pub enum DeclKind {
    Use {
        item: Spanned<UseItem>,
    },
    Mod {
        name: Spanned<Ident>,
    },
    Type {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
        ty: Spanned<Ty>,
    },
    ExternType {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
    },
    Struct {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
        fields: SpanSeq<StructField>,
    },
    Enum {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
        variants: SpanSeq<EnumVariant>,
    },
    Fn {
        name: Spanned<Ident>,
        params: SpanSeq<Parameter>,
        ret_ty: Option<Spanned<Ty>>,
        body: SpanBox<FnBody>,
    },
    ExternFn {
        name: Spanned<Ident>,
        params: SpanSeq<Parameter>,
        ret_ty: Option<Spanned<Ty>>,
    },
    Const {
        name: Spanned<Ident>,
        ty: Spanned<Ty>,
        value: Spanned<Expr>,
    },
}

#[derive(Debug, Clone)]
pub enum UseItem {
    Name(Spanned<Name>),
    Glob {
        root: Spanned<Name>,
    },
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
pub struct StructField {
    pub doc_comment: Option<Span>,
    pub attributes: SpanSeq<Attr>,
    pub visibility: Visibility,
    pub mutability: Mutability,
    pub name: Spanned<Ident>,
    pub ty: Spanned<Ty>,
}

#[derive(Debug, Clone, Copy, Default)]
pub enum Mutability {
    Mut(Span),
    #[default]
    Immut,
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub doc_comment: Option<Span>,
    pub attributes: SpanSeq<Attr>,
    pub name: Spanned<Ident>,
    pub payload: SpanSeq<Ty>,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub pattern: Spanned<Pattern>,
    pub ty: Option<Spanned<Ty>>,
}

#[derive(Debug, Clone)]
pub enum FnBody {
    EqExpr(Spanned<Expr>),
    Block(Spanned<Block>),
}

// ATTRIBUTES

#[derive(Debug, Clone)]
pub struct Attr {
    pub name: Name,
    pub args: SpanSeq<AttrArg>,
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
    Paren(SpanBox<Self>),
    Block(SpanBox<Block>),
    Struct {
        name: Spanned<Name>,
        fields: SpanSeq<StructExprField>,
        base: Option<SpanBox<Self>>,
    },
    Field {
        item: SpanBox<Self>,
        field: Spanned<FieldExprField>,
    },
    Lambda {
        params: Spanned<LambdaParams>,
        body: SpanBox<Self>,
    },
    Call {
        callee: SpanBox<Self>,
        args: SpanSeq<Self>,
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
        scrutinee: SpanBox<Self>,
        arms: SpanSeq<MatchArm>,
    },
    IfElse {
        condition: SpanBox<Self>,
        consequence: SpanBox<Block>,
        alternative: Option<SpanBox<Block>>,
    },
}

#[derive(Debug, Clone, Copy)]
pub enum LiteralExpr {
    Unit,
    True,
    False,
    Char(char),
    String,
    Int(i64),
    Float(f64),
}

#[derive(Debug, Clone)]
pub struct StructExprField {
    pub name: Spanned<Ident>,
    pub value: Option<Expr>,
}

#[derive(Debug, Clone)]
pub enum FieldExprField {
    Ident,
    Tuple(u16),
}

#[derive(Debug, Clone)]
pub enum LambdaParams {
    Ident,
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
    LeftPipe,
    RightPipe,
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
    pub statements: SpanSeq<Stmt>,
    pub ret_expr: Option<Spanned<Expr>>,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    Empty,
    Expr(Spanned<Expr>),
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
    Name(Spanned<Name>),
    Literal(Spanned<LiteralExpr>),
    Tuple(SpanSeq<Self>),
    List(SpanSeq<Self>),
    Paren(SpanBox<Self>),
    Cons {
        head: SpanBox<Self>,
        tail: SpanBox<Self>,
    },
    Enum {
        name: Spanned<Name>,
        elems: SpanSeq<Self>,
    },
    Struct {
        name: Spanned<Name>,
        fields: SpanSeq<StructPatternField>,
        rest: Option<Span>,
    },
}

#[derive(Debug, Clone)]
pub struct StructPatternField {
    pub field: Spanned<Name>,
    pub pattern: Option<Spanned<Pattern>>,
}

// TYPES

#[derive(Debug, Clone)]
pub enum Ty {
    Infer,
    Name,
    Prim(PrimTy),
    Tuple(SpanSeq<Self>),
    Paren(SpanBox<Self>),
    Fn {
        args: SpanBox<FnTyArgs>,
        ret: SpanBox<Self>,
    },
    Generic {
        name: Spanned<Name>,
        params: SpanSeq<Self>,
    },
}

#[derive(Debug, Clone)]
pub enum PrimTy {
    Never,
    Unit,
    Bool,
    Char,
    String,
    Int,
    Float,
}

#[derive(Debug, Clone)]
pub enum FnTyArgs {
    NoParens(Ty),
    Parens(SpanSeq<Ty>),
}

// NAMES

#[derive(Debug, Clone)]
pub enum Name {
    Path(SpanSeq<Ident>),
    Ident,
}

#[derive(Debug, Clone, Copy)]
pub struct Ident;
