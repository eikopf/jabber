//! Generic R6RS Scheme IR.

use std::collections::HashMap;

use crate::symbol::{StringInterner, Symbol};
use pretty::RcDoc;
use recursion::{
    Collapsible, CollapsibleExt, Expandable, MappableFrame, PartiallyApplied,
};

use super::blame::{BlameSeq, Blamed};

#[derive(Debug, Clone)]
pub struct Module {
    pub name: Symbol,
    pub public_items: BlameSeq<Symbol>,
    pub submodules: BlameSeq<Self>,
    pub definitions: HashMap<Symbol, Blamed<Expr>>,
}

#[derive(Debug, Clone)]
pub enum Expr {
    /// An expression of the form `(let (<bindings>) <body>)` (R6RS §5.2, §11.4.6).
    Let {
        bindings: Box<[(Symbol, Self)]>,
        body: Box<Self>,
    },
    /// An expression of the form `(<callee> <args>)`.
    Call {
        callee: Box<Self>,
        args: Box<[Self]>,
    },
    /// A lambda expression of the form `(lambda [<args>] <body>)`.
    Lambda {
        args: Box<[Symbol]>,
        body: Box<Self>,
    },
    /// The racket `(match val-expr clause ...)` form (Racket Reference §9).
    Match {
        scrutinee: Box<Self>,
        arms: Box<[MatchArm]>,
    },
    /// The racket `(match-let* ...)` form (Racket Reference §9).
    MatchLetSeq {
        bindings: Box<[(Pattern, Self)]>,
        body: Box<Self>,
    },
    /// The racket `(match-lambda** [(<patterns>) <body>])` form (Racket Reference §9).
    MatchLambdaVariadic {
        patterns: Box<[Pattern]>,
        body: Box<Self>,
    },
    /// A [`Literal`] expression.
    Literal(Literal),
    /// A [`Builtin`] expression.
    Builtin(Builtin),
    /// A plain identifier.
    Symbol(Symbol),
}

#[derive(Debug, Clone)]
pub struct MatchArm<A = Expr> {
    pub pattern: Pattern,
    pub body: A,
}

/// A subset of the racket pattern grammar.
#[derive(Debug, Clone)]
pub enum Pattern {
    Wildcard,
    Literal(Literal),
    Ident(Symbol),
    Cons { head: Box<Self>, tail: Box<Self> },
    Box(Box<Self>),
    List(Box<[Self]>),
    Vector(Box<[Self]>),
}

impl Pattern {
    pub fn nil() -> Self {
        Pattern::List(Default::default())
    }

    pub fn to_doc(
        self,
        interner: &mut StringInterner,
    ) -> Option<RcDoc<'static, ()>> {
        self.try_collapse_frames(|frame| frame.to_opt_doc(interner).ok_or(()))
            .ok()
    }
}

impl Expandable for Expr {
    type FrameToken = ExprFrame<PartiallyApplied>;

    fn from_frame(
        value: <Self::FrameToken as MappableFrame>::Frame<Self>,
    ) -> Self {
        match value {
            ExprFrame::Let { bindings, body } => Expr::Let {
                bindings,
                body: Box::new(body),
            },
            ExprFrame::Call { callee, args } => Expr::Call {
                callee: Box::new(callee),
                args,
            },
            ExprFrame::Lambda { args, body } => Expr::Lambda {
                args,
                body: Box::new(body),
            },
            ExprFrame::Match { scrutinee, arms } => Expr::Match {
                scrutinee: Box::new(scrutinee),
                arms,
            },
            ExprFrame::MatchLetSeq { bindings, body } => Expr::MatchLetSeq {
                bindings,
                body: Box::new(body),
            },
            ExprFrame::MatchLambdaVariadic { patterns, body } => {
                Expr::MatchLambdaVariadic {
                    patterns,
                    body: Box::new(body),
                }
            }
            ExprFrame::Literal(literal) => Expr::Literal(literal),
            ExprFrame::Builtin(builtin) => Expr::Builtin(builtin),
            ExprFrame::Variable(var) => Expr::Symbol(var),
        }
    }
}

impl Collapsible for Expr {
    type FrameToken = ExprFrame<PartiallyApplied>;

    fn into_frame(self) -> <Self::FrameToken as MappableFrame>::Frame<Self> {
        match self {
            Expr::Let { bindings, body } => ExprFrame::Let {
                bindings,
                body: *body,
            },
            Expr::Call { callee, args } => ExprFrame::Call {
                callee: *callee,
                args,
            },
            Expr::Lambda { args, body } => {
                ExprFrame::Lambda { args, body: *body }
            }
            Expr::Match { scrutinee, arms } => ExprFrame::Match {
                scrutinee: *scrutinee,
                arms,
            },
            Expr::MatchLetSeq { bindings, body } => ExprFrame::MatchLetSeq {
                bindings,
                body: *body,
            },
            Expr::MatchLambdaVariadic { patterns, body } => {
                ExprFrame::MatchLambdaVariadic {
                    patterns,
                    body: *body,
                }
            }
            Expr::Literal(literal) => ExprFrame::Literal(literal),
            Expr::Builtin(builtin) => ExprFrame::Builtin(builtin),
            Expr::Symbol(var) => ExprFrame::Variable(var),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprFrame<A> {
    Let {
        bindings: Box<[(Symbol, A)]>,
        body: A,
    },
    Call {
        callee: A,
        args: Box<[A]>,
    },
    Lambda {
        args: Box<[Symbol]>,
        body: A,
    },
    Match {
        scrutinee: A,
        arms: Box<[MatchArm<A>]>,
    },
    MatchLetSeq {
        bindings: Box<[(Pattern, A)]>,
        body: A,
    },
    MatchLambdaVariadic {
        patterns: Box<[Pattern]>,
        body: A,
    },
    Literal(Literal),
    Builtin(Builtin),
    Variable(Symbol),
}

impl MappableFrame for ExprFrame<PartiallyApplied> {
    type Frame<X> = ExprFrame<X>;

    fn map_frame<A, B>(
        input: Self::Frame<A>,
        mut f: impl FnMut(A) -> B,
    ) -> Self::Frame<B> {
        match input {
            ExprFrame::Let { bindings, body } => ExprFrame::Let {
                bindings: bindings
                    .into_iter()
                    .map(|(name, body)| (name, f(body)))
                    .collect(),
                body: f(body),
            },
            ExprFrame::Call { callee, args } => ExprFrame::Call {
                callee: f(callee),
                args: args.into_iter().map(f).collect(),
            },
            ExprFrame::Lambda { args, body } => ExprFrame::Lambda {
                args,
                body: f(body),
            },
            ExprFrame::Match { scrutinee, arms } => ExprFrame::Match {
                scrutinee: f(scrutinee),
                arms: arms
                    .into_iter()
                    .map(|MatchArm { pattern, body }| MatchArm {
                        pattern,
                        body: f(body),
                    })
                    .collect(),
            },
            ExprFrame::MatchLetSeq { bindings, body } => {
                ExprFrame::MatchLetSeq {
                    bindings: bindings
                        .into_iter()
                        .map(|(pat, rhs)| (pat, f(rhs)))
                        .collect(),
                    body: f(body),
                }
            }
            ExprFrame::MatchLambdaVariadic { patterns, body } => {
                ExprFrame::MatchLambdaVariadic {
                    patterns,
                    body: f(body),
                }
            }
            ExprFrame::Literal(literal) => ExprFrame::Literal(literal),
            ExprFrame::Builtin(builtin) => ExprFrame::Builtin(builtin),
            ExprFrame::Variable(var) => ExprFrame::Variable(var),
        }
    }
}

impl Expandable for Pattern {
    type FrameToken = PatternFrame<PartiallyApplied>;

    fn from_frame(
        val: <Self::FrameToken as MappableFrame>::Frame<Self>,
    ) -> Self {
        match val {
            PatternFrame::Wildcard => Pattern::Wildcard,
            PatternFrame::Literal(literal) => Pattern::Literal(literal),
            PatternFrame::Ident(symbol) => Pattern::Ident(symbol),
            PatternFrame::Cons { head, tail } => Pattern::Cons {
                head: Box::new(head),
                tail: Box::new(tail),
            },
            PatternFrame::Box(inner) => Pattern::Box(Box::new(inner)),
            PatternFrame::List(elems) => Pattern::List(elems),
            PatternFrame::Vector(elems) => Pattern::Vector(elems),
        }
    }
}

impl Collapsible for Pattern {
    type FrameToken = PatternFrame<PartiallyApplied>;

    fn into_frame(self) -> <Self::FrameToken as MappableFrame>::Frame<Self> {
        match self {
            Pattern::Wildcard => PatternFrame::Wildcard,
            Pattern::Literal(literal) => PatternFrame::Literal(literal),
            Pattern::Ident(symbol) => PatternFrame::Ident(symbol),
            Pattern::Cons { head, tail } => PatternFrame::Cons {
                head: *head,
                tail: *tail,
            },
            Pattern::Box(inner) => PatternFrame::Box(*inner),
            Pattern::List(elems) => PatternFrame::List(elems),
            Pattern::Vector(elems) => PatternFrame::Vector(elems),
        }
    }
}

#[derive(Debug, Clone)]
pub enum PatternFrame<A> {
    Wildcard,
    Literal(Literal),
    Ident(Symbol),
    Cons { head: A, tail: A },
    Box(A),
    List(Box<[A]>),
    Vector(Box<[A]>),
}

impl MappableFrame for PatternFrame<PartiallyApplied> {
    type Frame<X> = PatternFrame<X>;

    fn map_frame<A, B>(
        input: Self::Frame<A>,
        mut f: impl FnMut(A) -> B,
    ) -> Self::Frame<B> {
        match input {
            PatternFrame::Wildcard => PatternFrame::Wildcard,
            PatternFrame::Literal(literal) => PatternFrame::Literal(literal),
            PatternFrame::Ident(symbol) => PatternFrame::Ident(symbol),
            PatternFrame::Cons { head, tail } => PatternFrame::Cons {
                head: f(head),
                tail: f(tail),
            },
            PatternFrame::Box(inner) => PatternFrame::Box(f(inner)),
            PatternFrame::List(elems) => {
                PatternFrame::List(elems.into_iter().map(f).collect())
            }
            PatternFrame::Vector(elems) => {
                PatternFrame::Vector(elems.into_iter().map(f).collect())
            }
        }
    }
}

impl ExprFrame<RcDoc<'static, ()>> {
    pub fn to_opt_doc(
        self,
        interner: &mut StringInterner,
    ) -> Option<RcDoc<'static, ()>> {
        match self {
            ExprFrame::Let { bindings, body } => {
                let bindings = bindings
                    .iter()
                    .cloned()
                    .try_fold(
                        Vec::with_capacity(bindings.len()),
                        |mut bindings, (name, value)| {
                            let name = interner.resolve(name)?;
                            let doc = RcDoc::text("[")
                                .append(RcDoc::as_string(name))
                                .append(RcDoc::space())
                                .append(value)
                                .append(RcDoc::text("]"));
                            bindings.push(doc);
                            Some(bindings)
                        },
                    )?
                    .into_boxed_slice();

                Some(
                    RcDoc::text("(")
                        .append(RcDoc::text("let"))
                        .append(RcDoc::softline())
                        .append(RcDoc::text("["))
                        .append(RcDoc::intersperse(bindings, RcDoc::line()))
                        .append(RcDoc::text("]"))
                        .append(RcDoc::hardline().append(body).nest(2))
                        .append(RcDoc::text(")")),
                )
            }
            ExprFrame::Call { callee, args } => Some(
                RcDoc::text("(")
                    .append(callee)
                    .append(RcDoc::softline())
                    .append(RcDoc::intersperse(args, RcDoc::space()).group())
                    .append(")"),
            ),
            ExprFrame::Lambda { args, body } => {
                let args = args
                    .iter()
                    .try_fold(
                        Vec::with_capacity(args.len()),
                        |mut args, arg| {
                            let arg = interner.resolve(*arg)?;
                            args.push(RcDoc::as_string(arg));
                            Some(args)
                        },
                    )?
                    .into_boxed_slice();

                Some(
                    RcDoc::text("(")
                        .append(RcDoc::text("lambda"))
                        .append(RcDoc::space())
                        .append(RcDoc::group(
                            RcDoc::text("[")
                                .append(RcDoc::intersperse(
                                    args,
                                    RcDoc::space(),
                                ))
                                .append(RcDoc::text("]")),
                        ))
                        .append(RcDoc::line().append(body).nest(2))
                        .append(RcDoc::text(")")),
                )
            }
            ExprFrame::Match { scrutinee, arms } => {
                let arms =
                    arms.into_iter().map(|MatchArm { pattern, body }| {
                        RcDoc::text("[")
                            .append(pattern.to_doc(interner))
                            .append(RcDoc::space())
                            .append(body)
                            .append(RcDoc::text("]"))
                    });

                Some(
                    RcDoc::text("(")
                        .append(RcDoc::text("match"))
                        .append(RcDoc::space())
                        .append(scrutinee)
                        .append(RcDoc::line().nest(2))
                        .append(RcDoc::intersperse(arms, RcDoc::line()))
                        .append(RcDoc::text(")")),
                )
            }
            ExprFrame::MatchLetSeq { bindings, body } => {
                let bindings = bindings.into_iter().map(|(pat, rhs)| {
                    RcDoc::text("[")
                        .append(pat.to_doc(interner))
                        .append(RcDoc::softline())
                        .append(rhs)
                        .append("]")
                });

                Some(
                    RcDoc::text("(")
                        .append("match-let*")
                        .append(RcDoc::softline())
                        .append(RcDoc::group(
                            RcDoc::text("[")
                                .append(RcDoc::intersperse(
                                    bindings,
                                    RcDoc::softline(),
                                ))
                                .append("]"),
                        ))
                        .append(RcDoc::line())
                        .append(body)
                        .append(")"),
                )
            }
            ExprFrame::MatchLambdaVariadic { patterns, body } => {
                let patterns = RcDoc::text("(")
                    .append(RcDoc::intersperse(
                        patterns.into_iter().map(|pat| pat.to_doc(interner)),
                        RcDoc::space(),
                    ))
                    .append(RcDoc::text(")"));

                Some(
                    RcDoc::text("(")
                        .append(RcDoc::text("match-lambda**"))
                        .append(RcDoc::softline().nest(2))
                        .append(RcDoc::group(
                            RcDoc::text("[")
                                .append(patterns)
                                .append(RcDoc::softline())
                                .append(body)
                                .append(RcDoc::text("]")),
                        ))
                        .append(RcDoc::text(")")),
                )
            }
            ExprFrame::Literal(literal) => literal.to_opt_doc(interner),
            ExprFrame::Builtin(builtin) => {
                Some(RcDoc::as_string(builtin.identifier()))
            }
            ExprFrame::Variable(symbol) => {
                Some(RcDoc::as_string(interner.resolve(symbol)?))
            }
        }
    }
}

impl PatternFrame<RcDoc<'static, ()>> {
    pub fn to_opt_doc(
        self,
        interner: &mut StringInterner,
    ) -> Option<RcDoc<'static, ()>> {
        match self {
            PatternFrame::Wildcard => Some(RcDoc::text("_")),
            PatternFrame::Literal(literal) => literal.to_opt_doc(interner),
            PatternFrame::Ident(symbol) => {
                let symbol = interner.resolve(symbol)?;
                Some(
                    RcDoc::text("(var ")
                        .append(RcDoc::as_string(symbol))
                        .append(RcDoc::text(")")),
                )
            }
            PatternFrame::Cons { head, tail } => Some(
                RcDoc::text("(cons ")
                    .append(head)
                    .append(RcDoc::space())
                    .append(tail)
                    .append(RcDoc::text(")")),
            ),
            PatternFrame::Box(inner) => Some(
                RcDoc::text("(box ").append(inner).append(RcDoc::text(")")),
            ),
            PatternFrame::List(elems) => Some(
                RcDoc::text("(")
                    .append(RcDoc::text("list"))
                    .append(RcDoc::space())
                    .append(RcDoc::intersperse(elems, RcDoc::space()))
                    .append(")"),
            ),
            PatternFrame::Vector(elems) => Some(
                RcDoc::text("(")
                    .append(RcDoc::text("vector"))
                    .append(RcDoc::space())
                    .append(RcDoc::intersperse(elems, RcDoc::space()))
                    .append(")"),
            ),
        }
    }
}

/// A literal Scheme expression.
#[derive(Debug, Clone, Copy)]
pub enum Literal {
    /// The literal `#t` (R6RS §11.8).
    True,
    /// The literal `#f` (R6RS §11.8).
    False,
    /// A character literal, in particular a Unicode scalar value (R6RS §11.11).
    Char(char),
    /// A string literal, e.g. `"hello, world!"` (R6RS §11.12).
    String(Symbol),
    /// A symbol literal, e.g. `'sydney` (R6RS §11.10).
    Symbol(Symbol),
    /// A positive integer literal, e.g.`11`.
    UInt(u64),
    /// An IEEE-764 64-bit float literal, e.g. `13.4`.
    Float(f64),
}

impl Literal {
    pub fn to_opt_doc(
        &self,
        interner: &mut StringInterner,
    ) -> Option<RcDoc<'static, ()>> {
        Some(match self {
            Literal::True => RcDoc::text("#t"),
            Literal::False => RcDoc::text("#f"),
            Literal::Char(value) => RcDoc::as_string(format!("#\\{value}")),
            Literal::String(content) => {
                let content = interner.resolve(*content)?;
                RcDoc::text("\"")
                    .append(RcDoc::as_string(content))
                    .append(RcDoc::text("\""))
                    .group()
            }
            Literal::Symbol(symbol) => {
                let symbol = interner.resolve(*symbol)?;
                // TODO: verify `symbol` is a valid R6RS symbol
                RcDoc::text("`").append(RcDoc::as_string(symbol))
            }
            Literal::UInt(value) => RcDoc::as_string(format!("#e{value}")),
            Literal::Float(value) => RcDoc::as_string(format!("#i{value}")),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    Void,

    // BOXED VALUES
    Box,
    IsBox,
    Unbox,
    SetBox,

    // EQUIVALENCE (R6RS §11.5)
    /// Structural equality in the sense of OCaml's `=`.
    StructuralEq,
    /// Physical equality in the sense of OCaml's `==`.
    PhysicalEq,

    // FLOAT BUILTINS (R6RS Libraries §11.3)
    RealToFlonum,
    FlEq,
    FlLt,
    FlLe,
    FlGt,
    FlGe,
    FlPlus,
    FlMinus,
    FlStar,
    FlSlash,
    FlExpt,
    FlMax,
    FlMin,
    FlAbs,

    // GENERAL NUMERIC BUILTINS (R6RS Libraries §11)
    NumEq,
    Lt,
    Le,
    Gt,
    Ge,
    Plus,
    Minus,
    Star,
    Slash,
    Expt,
    Max,
    Min,
    Abs,
    Div,
    Mod,

    // BOOLEAN BUILTINS (R6RS §11.8)
    Not,
    And,
    Or,
    Xor,

    // LIST BUILTINS (R6RS §11.9)
    Car,
    Cdr,
    Cons,
    List,
    Length,
    Append,
    Map,

    // SYMBOL BUILTINS (R6RS §11.10)
    SymbolToString,
    SymbolEq,

    // CHARACTER BUILTINS (R6RS §11.11)
    CharToInteger,
    IntegerToChar,
    CharEq,
    CharLt,
    CharLe,
    CharGt,
    CharGe,

    // STRING BUILTINS (R6RS §11.12)
    String,
    StringLength,
    StringRef,
    StringEq,
    Substring,
    StringAppend,
    StringToList,
    ListToString,

    // VECTOR BULTINS (R6RS §11.13)
    Vector,
    VectorLength,
    VectorSet,
    VectorRef,
    VectorToList,
    ListToVector,
    VectorMap,
}

impl Builtin {
    pub const fn identifier(&self) -> &'static str {
        match self {
            Self::Void => "void",

            // BOXES
            Self::Box => "box",
            Self::IsBox => "box?",
            Self::Unbox => "unbox",
            Self::SetBox => "set-box!",

            // EQUIVALENCE
            Self::StructuralEq => "equal?",
            Self::PhysicalEq => "eq?",

            // FLOAT
            Self::RealToFlonum => "real->flonum",
            Self::FlEq => "fl=",
            Self::FlLt => "fl<",
            Self::FlLe => "fl<=",
            Self::FlGe => "fl>",
            Self::FlGt => "fl>=",
            Self::FlPlus => "fl+",
            Self::FlMinus => "fl-",
            Self::FlStar => "fl*",
            Self::FlSlash => "fl/",
            Self::FlExpt => "flexpt",
            Self::FlMax => "flmax",
            Self::FlMin => "flmin",
            Self::FlAbs => "flabs",

            // GENERAL NUMERIC
            Self::NumEq => "=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Gt => ">",
            Self::Ge => ">=",
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Slash => "/",
            Self::Expt => "expt",
            Self::Max => "max",
            Self::Min => "min",
            Self::Abs => "abs",
            Self::Div => "div",
            Self::Mod => "mod",

            // BOOLEAN
            Self::Not => "not",
            Self::And => "and",
            Self::Or => "or",
            Self::Xor => "xor",

            // LIST
            Self::Car => "car",
            Self::Cdr => "cdr",
            Self::Cons => "cons",
            Self::List => "list",
            Self::Length => "length",
            Self::Append => "append",
            Self::Map => "map",

            // SYMBOL
            Self::SymbolToString => "symbol->string",
            Self::SymbolEq => "symbol=?",

            // CHARACTER
            Self::CharToInteger => "char->integer",
            Self::IntegerToChar => "integer->char",
            Self::CharEq => "char=?",
            Self::CharLt => "char<?",
            Self::CharLe => "char<=?",
            Self::CharGt => "char>?",
            Self::CharGe => "char>=?",

            // STRING
            Self::String => "string",
            Self::StringLength => "string-length",
            Self::StringRef => "string-ref",
            Self::StringEq => "string=?",
            Self::Substring => "substring",
            Self::StringAppend => "string-append",
            Self::StringToList => "string->list",
            Self::ListToString => "list->string",

            // VECTOR
            Self::Vector => "vector",
            Self::VectorLength => "vector-length",
            Self::VectorSet => "vector-set!",
            Self::VectorRef => "vector-ref",
            Self::VectorToList => "vector->list",
            Self::ListToVector => "list->vector",
            Self::VectorMap => "vector-map",
        }
    }
}

/// The contents of a `define-record-type` form.
#[derive(Debug, Clone)]
pub struct RecordDefinition {
    pub name: Symbol,
    pub fields: Box<[RecordField]>,
}

#[derive(Debug, Clone, Copy)]
pub struct RecordField {
    pub mutability: Mutability,
    pub name: Symbol,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mutability {
    Mutable,
    Immutable,
}

#[cfg(test)]
mod tests {
    use recursion::CollapsibleExt;

    use super::*;

    macro_rules! symbol {
        ($sym:expr) => {
            super::Expr::Symbol($sym)
        };
    }

    macro_rules! call {
        ($callee:expr, $($arg:expr),*) => {
            super::Expr::Call {
                callee: std::boxed::Box::new($callee),
                args: vec![$($arg,)*].into_boxed_slice(),
            }
        };
    }

    macro_rules! r#let {
        ([$([$lhs:expr, $rhs:expr]),*] $body:expr) => {
            super::Expr::Let {
                bindings: vec![$(($lhs, $rhs)),*].into_boxed_slice(),
                body: std::boxed::Box::new($body),
            }
        };
    }

    macro_rules! lambda {
        ([$($param:expr),*] $body:expr) => {
            super::Expr::Lambda {
                args: vec![$($param,)*].into_boxed_slice(),
                body: std::boxed::Box::new($body),
            }
        };
    }

    #[test]
    fn simple_doc_printing() {
        let mut interner = crate::symbol::StringInterner::new();
        let x = interner.intern_static("x");
        let y = interner.intern_static("y");
        let add = interner.intern_static("add");

        let expr = r#let!([[add, Expr::Builtin(Builtin::Plus)]]
                        lambda!([x, y]
                            call!(symbol!(add), symbol!(x), symbol!(y))));

        let doc = expr
            .collapse_frames(|frame| frame.to_opt_doc(&mut interner).unwrap());

        let repr = format!("{}", doc.pretty(80));
        eprintln!("{repr}");
        assert_eq!(repr, "(let [[add +]]\n  (lambda [x y]\n    (add x y)))");
    }

    #[test]
    fn match_lambda_var_printing() {
        let mut interner = crate::symbol::StringInterner::new();
        let contents = interner.intern_static("contents");

        let expr = Expr::MatchLambdaVariadic {
            patterns: vec![Pattern::Box(Box::new(Pattern::Ident(contents)))]
                .into_boxed_slice(),
            body: Box::new(symbol!(contents)),
        };

        let doc = expr
            .collapse_frames(|frame| frame.to_opt_doc(&mut interner).unwrap());
        let repr = format!("{}", doc.pretty(80));
        eprintln!("{repr}");
        assert_eq!(repr, "(match-lambda** [((box (var contents))) contents])");
    }
}
