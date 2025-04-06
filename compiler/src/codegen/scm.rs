//! Generic R6RS Scheme IR.

use crate::symbol::{StringInterner, Symbol};
use pretty::{Doc, RcDoc};
use recursion::{Collapsible, Expandable, MappableFrame, PartiallyApplied};

#[derive(Debug, Clone)]
pub enum Expr {
    /// An expression of the form `(define <variable> <expr>)` (R6RS §11.2).
    Define { name: Symbol, body: Box<Self> },
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
    /// A linked-list constant, e.g. `'(x 1 #t)` or `'()`.
    List(Box<[Self]>),
    /// A vector constant, e.g. `'#(14 (8 2 3) "hello")`.
    Vector(Box<[Self]>),
    /// A [`Literal`] expression.
    Literal(Literal),
    /// A [`Builtin`] expression.
    Builtin(Builtin),
    /// A plain identifier.
    Variable(Symbol),
}

impl Expandable for Expr {
    type FrameToken = ExprFrame<PartiallyApplied>;

    fn from_frame(
        value: <Self::FrameToken as MappableFrame>::Frame<Self>,
    ) -> Self {
        match value {
            ExprFrame::Define { name, body } => Expr::Define {
                name,
                body: Box::new(body),
            },
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
            ExprFrame::List(elems) => Expr::List(elems),
            ExprFrame::Vector(elems) => Expr::Vector(elems),
            ExprFrame::Literal(literal) => Expr::Literal(literal),
            ExprFrame::Builtin(builtin) => Expr::Builtin(builtin),
            ExprFrame::Variable(var) => Expr::Variable(var),
        }
    }
}

impl Collapsible for Expr {
    type FrameToken = ExprFrame<PartiallyApplied>;

    fn into_frame(self) -> <Self::FrameToken as MappableFrame>::Frame<Self> {
        match self {
            Expr::Define { name, body } => {
                ExprFrame::Define { name, body: *body }
            }
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
            Expr::List(elems) => ExprFrame::List(elems),
            Expr::Vector(elems) => ExprFrame::Vector(elems),
            Expr::Literal(literal) => ExprFrame::Literal(literal),
            Expr::Builtin(builtin) => ExprFrame::Builtin(builtin),
            Expr::Variable(var) => ExprFrame::Variable(var),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ExprFrame<A> {
    Define {
        name: Symbol,
        body: A,
    },
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
    List(Box<[A]>),
    Vector(Box<[A]>),
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
            ExprFrame::Define { name, body } => ExprFrame::Define {
                name,
                body: f(body),
            },
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
            ExprFrame::List(elems) => {
                ExprFrame::List(elems.into_iter().map(f).collect())
            }
            ExprFrame::Vector(elems) => {
                ExprFrame::Vector(elems.into_iter().map(f).collect())
            }
            ExprFrame::Literal(literal) => ExprFrame::Literal(literal),
            ExprFrame::Builtin(builtin) => ExprFrame::Builtin(builtin),
            ExprFrame::Variable(var) => ExprFrame::Variable(var),
        }
    }
}

impl ExprFrame<RcDoc<'static, ()>> {
    pub fn to_doc(
        self,
        interner: &mut StringInterner,
    ) -> Option<RcDoc<'static, ()>> {
        match self {
            ExprFrame::Define { name, body } => {
                let name = interner.resolve(name)?;
                Some(
                    RcDoc::text("(")
                        .append(RcDoc::text("define"))
                        .append(RcDoc::softline())
                        .append(RcDoc::as_string(name))
                        .append(RcDoc::line().append(body).nest(1))
                        .append(RcDoc::text(")")),
                )
            }
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
                        .append(RcDoc::hardline().append(body).nest(1))
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
                        .append(RcDoc::line().append(body).nest(1))
                        .append(RcDoc::text(")")),
                )
            }
            ExprFrame::List(elems) => Some(
                RcDoc::text("'(")
                    .append(RcDoc::intersperse(elems, Doc::space()))
                    .append(RcDoc::text(")"))
                    .group(),
            ),
            ExprFrame::Vector(elems) => Some(
                RcDoc::text("'#(")
                    .append(RcDoc::intersperse(elems, Doc::space()))
                    .append(RcDoc::text(")"))
                    .group(),
            ),
            ExprFrame::Literal(literal) => literal.to_doc(interner),
            ExprFrame::Builtin(builtin) => {
                Some(RcDoc::as_string(builtin.identifier()))
            }
            ExprFrame::Variable(symbol) => {
                Some(RcDoc::as_string(interner.resolve(symbol)?))
            }
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
    pub fn to_doc(
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
                RcDoc::text("'").append(RcDoc::as_string(symbol)).group()
            }
            Literal::UInt(value) => RcDoc::as_string(format!("{value}")),
            Literal::Float(value) => RcDoc::as_string(format!("{value}")),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Builtin {
    Void,

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
    FlMax,
    FlMin,
    FlAbs,

    // GENERAL NUMERIC BUILTINS (R6RS Libraries §11)
    Plus,
    Minus,
    Star,
    Max,
    Min,
    Abs,
    Slash,
    Div,
    Mod,

    // BOOLEAN BUILTINS (R6RS §11.8)
    Not,

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
    VectorRef,
    VectorToList,
    ListToVector,
    VectorMap,
}

impl Builtin {
    pub const fn identifier(&self) -> &'static str {
        match self {
            Self::Void => "void",

            // FLOAT
            Self::RealToFlonum => "real->flonum",
            Self::FlEq => "fl=?",
            Self::FlLt => "fl<?",
            Self::FlLe => "fl<=?",
            Self::FlGe => "fl>?",
            Self::FlGt => "fl>=?",
            Self::FlPlus => "fl+",
            Self::FlMinus => "fl-",
            Self::FlStar => "fl*",
            Self::FlSlash => "fl/",
            Self::FlMax => "flmax",
            Self::FlMin => "flmin",
            Self::FlAbs => "flabs",

            // GENERAL NUMERIC
            Self::Plus => "+",
            Self::Minus => "-",
            Self::Star => "*",
            Self::Max => "max",
            Self::Min => "min",
            Self::Abs => "abs",
            Self::Slash => "/",
            Self::Div => "div",
            Self::Mod => "mod",

            // BOOLEAN
            Self::Not => "not",

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

    #[test]
    fn simple_doc_printing() {
        let mut interner = crate::symbol::StringInterner::new();
        let x = interner.intern_static("x");
        let y = interner.intern_static("y");
        let add = interner.intern_static("add");

        let expr = Expr::Define {
            name: add,
            body: Box::new(Expr::Lambda {
                args: vec![x, y].into_boxed_slice(),
                body: Box::new(Expr::Call {
                    callee: Box::new(Expr::Builtin(Builtin::Plus)),
                    args: vec![Expr::Variable(x), Expr::Variable(y)]
                        .into_boxed_slice(),
                }),
            }),
        };

        let doc =
            expr.collapse_frames(|frame| frame.to_doc(&mut interner).unwrap());

        let repr = format!("{}", doc.pretty(80));
        assert_eq!(repr, "(define add\n (lambda [x y]\n  (+ x y)))");
    }
}
