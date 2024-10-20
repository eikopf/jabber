//! Unbound ASTs derived from [`Cst`s](crate::cst::Cst).
//!
//! ASTs in this stage store almost everything in terms of [`Span`] data,
//! including in particular both identifiers and string literals. Literals
//! are unprocessed (except for `true` and `false`, which are trivial). No
//! syntax errors are present: ASTs are syntactically well-formed, but unbound
//! and untyped.
//!
//! # Spanning Data Conventions
//! Objects in this module do not store their own spanning information, and
//! only store spanning information for a member if that member's spanning
//! information cannot be inferred.
//!
//! As an example, [`Ty`] stores spanning information for all its members
//! except [`Ty::Infer`], [`Ty::Name`], and [`Ty::Prim`]. For those three
//! variants, their spanning information is exactly the same as the [`Span`]
//! represented in a [`Spanned<Ty>`].

use crate::{
    file::File,
    span::{Span, SpanBox, SpanSeq, Spanned},
};

#[derive(Debug, Clone)]
pub struct Ast<'a> {
    pub(super) file: &'a File,
    pub(super) shebang: Option<Span>,
    pub(super) module_comment: Option<Span>,
    pub(super) comments: Box<[Span]>,
    pub(super) decls: SpanSeq<Decl>,
}

impl<'a> Ast<'a> {
    pub fn new(
        file: &'a File,
        shebang: Option<Span>,
        module_comment: Option<Span>,
        comments: Box<[Span]>,
        decls: SpanSeq<Decl>,
    ) -> Self {
        Self {
            file,
            shebang,
            module_comment,
            comments,
            decls,
        }
    }

    pub fn file(&self) -> &File {
        self.file
    }

    pub fn shebang(&self) -> Option<Span> {
        self.shebang
    }

    pub fn module_comment(&self) -> Option<Span> {
        self.module_comment
    }

    pub fn comments(&self) -> &[Span] {
        &self.comments
    }

    pub fn decls(&self) -> &[Spanned<Decl>] {
        &self.decls
    }
}

// DECLARATIONS

#[derive(Debug, Clone)]
pub struct Decl {
    pub doc_comment: Option<Span>,
    pub attributes: SpanSeq<Attr>,
    pub visibility: Visibility,
    pub kind: DeclKind,
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
        params: Spanned<SpanSeq<Parameter>>,
        return_ty: Option<Spanned<Ty>>,
        body: SpanBox<FnBody>,
    },
    ExternFn {
        name: Spanned<Ident>,
        params: Spanned<SpanSeq<Parameter>>,
        return_ty: Option<Spanned<Ty>>,
    },
    Const {
        name: Spanned<Ident>,
        ty: Spanned<Ty>,
        value: Spanned<Expr>,
    },
}

#[derive(Debug, Clone)]
pub enum UseItem {
    Name(Name),
    Glob {
        root: Option<Spanned<Name>>,
    },
    Alias {
        item: Spanned<Name>,
        alias: Spanned<Ident>,
    },
    Tree {
        root: Option<Spanned<Name>>,
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
    EqExpr(Expr),
    Block(Block),
}

// ATTRIBUTES

#[derive(Debug, Clone)]
pub struct Attr {
    pub name: Spanned<Name>,
    pub args: SpanSeq<AttrArg>,
}

#[derive(Debug, Clone)]
pub enum AttrArg {
    Name(Name),
    Literal(LiteralExpr),
}

// EXPRESSIONS

#[derive(Debug, Clone)]
pub enum Expr {
    Name(Name),
    Literal(LiteralExpr),
    List(SpanSeq<Self>),
    Tuple(SpanSeq<Self>),
    Paren(SpanBox<Self>),
    Block(Box<Block>),
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
        arms: Spanned<SpanSeq<MatchArm>>,
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
    Bool(bool),
    Char,
    String,
    BinInt,
    OctInt,
    DecInt,
    HexInt,
    Float,
}

#[derive(Debug, Clone)]
pub struct StructExprField {
    pub name: Spanned<Ident>,
    pub value: Option<Spanned<Expr>>,
}

#[derive(Debug, Clone)]
pub enum FieldExprField {
    Ident,
    TupleIndex,
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
    pub return_expr: Option<Spanned<Expr>>,
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
    Name(Name),
    Literal(LiteralExpr),
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
    pub field: Spanned<Ident>,
    pub pattern: Option<Spanned<Pattern>>,
}

// TYPES

#[derive(Debug, Clone)]
pub enum Ty {
    Infer,
    Name(Name),
    Prim(PrimTy),
    Tuple(SpanSeq<Self>),
    Paren(SpanBox<Self>),
    Fn {
        domain: SpanBox<FnTyArgs>,
        codomain: SpanBox<Self>,
    },
    Generic {
        name: Spanned<Name>,
        args: SpanSeq<Self>,
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
