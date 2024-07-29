//! The [`Token`] type and its [`Logos`] lexer implementation.

use byteyarn::YarnBox;
use logos::{Lexer, Logos, Source};

#[derive(Debug, Clone, Logos)]
#[logos(skip r"[ \t\r\f\n]+")]
pub enum Token<'src> {
    // BRACKETS
    #[token("(")]
    LeftParen,
    #[token(")")]
    RightParen,
    #[token("[")]
    LeftBracket,
    #[token("]")]
    RightBracket,
    #[token("{")]
    LeftBrace,
    #[token("}")]
    RightBrace,

    // ARITHMETIC OPERATORS
    #[token("+")]
    Plus,
    #[token("-")]
    Minus,
    #[token("*")]
    Star,
    #[token("/")]
    Slash,
    #[token("%")]
    Percent,

    // LOGICAL OPERATORS
    #[token("&&")]
    And,
    #[token("||")]
    Or,

    // COMPARISON OPERATORS
    #[token("==")]
    EqEq,
    #[token("!=")]
    Neq,
    #[token("<=>")]
    Cmp,
    #[token("<")]
    Lt,
    #[token("<=")]
    Lte,
    #[token(">")]
    Gt,
    #[token(">=")]
    Gte,

    // SEQUENCE OPERATORS
    #[token("::")]
    Cons,
    #[token("++")]
    Concat,

    // FUNCTIONAL OPERATORS
    #[token("|>")]
    Pipe,
    #[token("$")]
    Dollar,
    #[token(">>=")]
    Bind,

    // PUNCTUATION
    #[token("=")]
    Eq,
    #[token(".")]
    Dot,
    #[token(",")]
    Comma,
    #[token(":")]
    Colon,
    #[token(";")]
    Semicolon,
    #[token("_")]
    Underscore,
    #[token("!")]
    Bang,
    #[token("?")]
    Hook,
    #[token("->")]
    RightArrow,
    #[token("=>")]
    FatRightArrow,

    // KEYWORDS
    #[token("mod", priority = 20)]
    Mod,
    #[token("pub")]
    Pub,
    #[token("use")]
    Use,
    #[token("const")]
    Const,
    #[token("enum")]
    Enum,
    #[token("struct")]
    Struct,
    #[token("def")]
    Def,
    #[token("let")]
    Let,
    #[token("match")]
    Match,
    #[token("if", priority = 20)]
    If,
    #[token("else")]
    Else,
    #[token("true")]
    True,
    #[token("false")]
    False,

    // PRIMITIVE TYPES
    #[token("()")]
    Unit,
    #[token("bool")]
    Bool,
    #[token("char")]
    Char,
    #[token("string")]
    String,
    #[token("u8", priority = 20)]
    U8,
    #[token("u16")]
    U16,
    #[token("u32")]
    U32,
    #[token("u64")]
    U64,
    #[token("i8", priority = 20)]
    I8,
    #[token("i16")]
    I16,
    #[token("i32")]
    I32,
    #[token("i64")]
    I64,
    #[token("f32")]
    F32,
    #[token("f64")]
    F64,

    // LITERALS
    #[regex(r#""(\\"|[^"\r])*""#, string_literal)]
    StringLiteral(Frag<'src>),
    #[regex(r#"[0-9]+\.[0-9]+(f32|f64)?"#, float_literal)]
    FloatLiteral(FloatLiteral<'src>),
    #[regex(r#"0b[01]+((u|i)(8|16|32|64))?"#, num_literal)]
    BinLiteral(NumLiteral<'src, Bin>),
    #[regex(r#"0o[0-7]+((u|i)(8|16|32|64))?"#, num_literal)]
    OctLiteral(NumLiteral<'src, Oct>),
    #[regex(r#"[0-9]+(((u|i)(8|16|32|64))|f32|f64)?"#, num_literal)]
    DecLiteral(NumLiteral<'src, Dec>),
    #[regex(r#"0(x|X)[0-9a-fA-F]+((u|i)(8|16|32|64))?"#, num_literal)]
    HexLiteral(NumLiteral<'src, Hex>),

    // IDENTIFIERS
    #[regex(r#"\.(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*"#, projection)]
    Projection(Frag<'src>),
    #[regex(r#"(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*"#, fragment)]
    Ident(Frag<'src>),
    #[regex(
        r#"(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*(::(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*)+"#,
        name
    )]
    Name(Name<'src>),
}

/// A literal fragment of the source.
type Frag<'src> = YarnBox<'src, str>;
type LexInput<'src> = Lexer<'src, Token<'src>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FloatLiteral<'src> {
    value: Frag<'src>,
    point_offset: u32,
    suffix: Option<FloatSuffix>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum FloatSuffix {
    F32,
    F64,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct NumLiteral<'src, R: Radix> {
    value: Frag<'src>,
    suffix: Option<R::Suffix>,
    radix: std::marker::PhantomData<R>,
}

pub trait Radix {
    type Suffix;

    fn strip_prefix(s: &str) -> Option<&str>;

    fn strip_suffix(s: &str) -> (&str, Option<Self::Suffix>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Bin;
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Oct;
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Dec;
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Hex;

impl Radix for Bin {
    type Suffix = IntSuffix;

    fn strip_prefix(s: &str) -> Option<&str> {
        s.strip_prefix("0b")
    }

    fn strip_suffix(s: &str) -> (&str, Option<Self::Suffix>) {
        strip_int_suffix(s)
    }
}

impl Radix for Oct {
    type Suffix = IntSuffix;

    fn strip_prefix(s: &str) -> Option<&str> {
        s.strip_prefix("0o")
    }

    fn strip_suffix(s: &str) -> (&str, Option<Self::Suffix>) {
        strip_int_suffix(s)
    }
}

impl Radix for Dec {
    type Suffix = DecSuffix;

    fn strip_prefix(s: &str) -> Option<&str> {
        // decimal values have no prefix
        Some(s)
    }

    fn strip_suffix(s: &str) -> (&str, Option<Self::Suffix>) {
        let (suffix, offset) = if s.ends_with("u8") {
            (Some(DecSuffix::U8), 2)
        } else if s.ends_with("u16") {
            (Some(DecSuffix::U16), 3)
        } else if s.ends_with("u32") {
            (Some(DecSuffix::U32), 3)
        } else if s.ends_with("u64") {
            (Some(DecSuffix::U64), 3)
        } else if s.ends_with("i8") {
            (Some(DecSuffix::I8), 2)
        } else if s.ends_with("i16") {
            (Some(DecSuffix::I16), 3)
        } else if s.ends_with("i32") {
            (Some(DecSuffix::I32), 3)
        } else if s.ends_with("i64") {
            (Some(DecSuffix::I64), 3)
        } else if s.ends_with("f32") {
            (Some(DecSuffix::F32), 3)
        } else if s.ends_with("f64") {
            (Some(DecSuffix::F64), 3)
        } else {
            (None, 0)
        };

        (&s[..(s.len() - offset)], suffix)
    }
}

impl Radix for Hex {
    type Suffix = IntSuffix;

    fn strip_prefix(s: &str) -> Option<&str> {
        s.strip_prefix("0x").or_else(|| s.strip_prefix("0X"))
    }

    fn strip_suffix(s: &str) -> (&str, Option<Self::Suffix>) {
        strip_int_suffix(s)
    }
}

fn strip_int_suffix(s: &str) -> (&str, Option<IntSuffix>) {
    let (suffix, offset) = if s.ends_with("u8") {
        (Some(IntSuffix::U8), 2)
    } else if s.ends_with("u16") {
        (Some(IntSuffix::U16), 3)
    } else if s.ends_with("u32") {
        (Some(IntSuffix::U32), 3)
    } else if s.ends_with("u64") {
        (Some(IntSuffix::U64), 3)
    } else if s.ends_with("i8") {
        (Some(IntSuffix::I8), 2)
    } else if s.ends_with("i16") {
        (Some(IntSuffix::I16), 3)
    } else if s.ends_with("i32") {
        (Some(IntSuffix::I32), 3)
    } else if s.ends_with("i64") {
        (Some(IntSuffix::I64), 3)
    } else {
        (None, 0)
    };

    (&s[..(s.len() - offset)], suffix)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum IntSuffix {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DecSuffix {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
}

#[derive(Debug, Clone)]
pub struct Name<'src>(Box<[Frag<'src>]>);

fn string_literal<'src>(lexer: &mut LexInput<'src>) -> Option<Frag<'src>> {
    let slice = lexer.slice();
    let content = slice.strip_prefix("\"")?.strip_suffix("\"")?;
    Some(YarnBox::new(content))
}

fn float_literal<'src>(lexer: &mut LexInput<'src>) -> Option<FloatLiteral<'src>> {
    let slice = lexer.slice();
    let (suffix, end_offset) = if slice.ends_with("f32") {
        (Some(FloatSuffix::F32), 3)
    } else if slice.ends_with("f64") {
        (Some(FloatSuffix::F64), 3)
    } else {
        (None, 0)
    };

    let point_offset: u32 = slice.find(".")?.try_into().ok()?;
    let value: Frag<'_> = slice[..(slice.len() - end_offset)].into();

    Some(FloatLiteral {
        value,
        point_offset,
        suffix,
    })
}

fn num_literal<'src, R>(lexer: &mut LexInput<'src>) -> Option<NumLiteral<'src, R>>
where
    R: Radix,
{
    let (value, suffix) = R::strip_suffix(lexer.slice());

    let value: Frag<'_> = R::strip_prefix(value)?.into();

    Some(NumLiteral {
        value,
        suffix,
        radix: std::marker::PhantomData,
    })
}

fn projection<'src>(lexer: &mut LexInput<'src>) -> Option<Frag<'src>> {
    let ident = lexer.slice().strip_prefix(".")?;
    Some(Frag::new(ident))
}

fn name<'src>(lexer: &mut LexInput<'src>) -> Name<'src> {
    let slice = lexer.slice();
    let components = slice.split("::").map(YarnBox::new).collect::<Box<[_]>>();
    Name(components)
}

fn fragment<'src>(lexer: &mut LexInput<'src>) -> Frag<'src> {
    YarnBox::new(lexer.slice())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lexer_testing() {
        let source = r#"
            def map(f: u8 -> T, list: List[u8]) = match list {
                []        => [],
                (x :: xs) => f(x) :: map(f, xs),
            }

            def std::operator::add(lhs: (), rhs: ()) = ()
            def std::operator::mul(lhs: (), rhs: ()) = ()

            pub enum Result[E, T] {
                Ok(T),
                Err(E),
            }

            def deep_inner(x: _) = x.y.z.w . foo

            const THING: string = "something, probably";

            const zero: u8 = 0x00;
            const one: u64 = 0b0001u64;
            const eight: i16 = 0o10;
            const f1: f32 = 13.32f32;
            const f2 = 0.1024f64;
            const f3 = 1000.32;
        "#;
        let lexer = Token::lexer(source);
        let tokens = lexer.into_iter().map(Result::unwrap).collect::<Vec<_>>();
        dbg!(tokens);
        panic!();
    }
}
