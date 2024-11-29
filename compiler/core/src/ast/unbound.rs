//! Unbound ASTs derived from [`Cst`s](crate::cst::Cst).
//!
//! ASTs in this stage store almost everything in terms of [`Span`] data,
//! and avoid copying and allocating as much as is possible. Literals are
//! unprocessed (except for `true` and `false`, for which it is trivial). No
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
    source_file::SourceFile,
    span::{Span, SpanBox, SpanSeq, Spanned},
};

use super::SpannedModuleTrivia;

pub use super::common::{Qualifier, Visibility};

#[derive(Debug, Clone)]
pub struct Ast {
    pub trivia: SpannedModuleTrivia,
    pub decls: SpanSeq<Decl>,
    pub file: SourceFile,
}

impl Ast {
    pub fn new(
        shebang: Option<Span>,
        module_comment: Option<Span>,
        comments: Box<[Span]>,
        decls: SpanSeq<Decl>,
        file: SourceFile,
    ) -> Self {
        Self {
            trivia: SpannedModuleTrivia {
                shebang,
                module_comment,
                comments,
            },
            decls,
            file,
        }
    }

    pub fn shebang(&self) -> Option<Span> {
        self.trivia.shebang
    }

    pub fn module_comment(&self) -> Option<Span> {
        self.trivia.module_comment
    }

    pub fn comments(&self) -> &[Span] {
        &self.trivia.comments
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
    pub kind: Spanned<DeclKind>,
}

#[derive(Debug, Clone)]
pub enum DeclKind {
    Use {
        item: Spanned<UseItem>,
    },
    Mod {
        name: Spanned<Ident>,
    },
    TypeAlias {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
        ty: Spanned<Ty>,
    },
    Type {
        name: Spanned<Ident>,
        opacity: Option<Span>,
        params: SpanSeq<Ident>,
        constructors: SpanSeq<TyConstr>,
    },
    ExternType {
        name: Spanned<Ident>,
        params: SpanSeq<Ident>,
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
        ty: Option<Spanned<Ty>>,
        value: Spanned<Expr>,
    },
}

#[derive(Debug, Clone)]
pub enum UseItem {
    Name(Name),
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
pub struct TyConstr {
    pub doc_comment: Option<Span>,
    pub attributes: SpanSeq<Attr>,
    pub name: Spanned<Ident>,
    pub payload: Option<Spanned<TyConstrPayload>>,
}

#[derive(Debug, Clone)]
pub enum TyConstrPayload {
    Tuple(SpanSeq<Ty>),
    Record(SpanSeq<RecordField>),
}

#[derive(Debug, Clone)]
pub struct RecordField {
    pub doc_comment: Option<Span>,
    pub attributes: SpanSeq<Attr>,
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
pub struct Parameter {
    pub pattern: Spanned<Pattern>,
    pub ty: Option<Spanned<Ty>>,
}

/// Note that the span in a `Spanned<FnBody>` always refers to the expression
/// or block payload, never the `=` prefix in the `EqExpr` case.
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
    Record {
        name: Spanned<Name>,
        fields: SpanSeq<RecordExprField>,
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

#[derive(Debug, Clone)]
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
pub struct RecordExprField {
    pub field: Spanned<Ident>,
    pub value: Option<Spanned<Expr>>,
}

#[derive(Debug, Clone)]
pub enum FieldExprField {
    Ident(Ident),
    TupleIndex,
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
    TupleConstr {
        name: Spanned<Name>,
        elems: SpanSeq<Self>,
    },
    Record {
        name: Spanned<Name>,
        fields: SpanSeq<RecordPatternField>,
        rest: Option<Span>,
    },
}

#[derive(Debug, Clone)]
pub struct RecordPatternField {
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

impl FnTyArgs {
    pub fn len(&self) -> usize {
        match self {
            FnTyArgs::NoParens(_) => 1,
            FnTyArgs::Parens(tys) => tys.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

// NAMES

#[derive(Debug, Clone)]
pub enum Name {
    Path(Option<Spanned<Qualifier>>, SpanSeq<Ident>),
    Ident(Ident),
}

#[derive(Debug, Clone, Copy)]
pub struct Ident;
