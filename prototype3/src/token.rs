//! The [`Token`] type and its [`Logos`] lexer implementation.

use byteyarn::YarnBox;
use logos::{Lexer, Logos};

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
    StringLiteral(YarnBox<'src, str>),
    #[regex(r#"[0-9]+\.[0-9]+(f32|f64)?"#, str_to_yarn)]
    FloatLiteral(YarnBox<'src, str>),
    #[regex(r#"0b[01]+((u|i)(8|16|32|64))?"#, str_to_yarn)]
    BinLiteral(YarnBox<'src, str>),
    #[regex(r#"0o[0-7]+((u|i)(8|16|32|64))?"#, str_to_yarn)]
    OctLiteral(YarnBox<'src, str>),
    #[regex(r#"[0-9]+(((u|i)(8|16|32|64))|f32|f64)?"#, str_to_yarn)]
    DecLiteral(YarnBox<'src, str>),
    #[regex(r#"0(x|X)[0-9a-fA-F]+((u|i)(8|16|32|64))?"#, str_to_yarn)]
    HexLiteral(YarnBox<'src, str>),

    // IDENTIFIERS
    #[regex(r#"\.(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*"#, str_to_yarn)]
    Projection(YarnBox<'src, str>),
    #[regex(r#"(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*"#, str_to_yarn)]
    Ident(YarnBox<'src, str>),
    #[regex(
        r#"(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*(::(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*)+"#,
        str_to_yarn
    )]
    Name(YarnBox<'src, str>),
}

fn string_literal<'src>(lexer: &mut Lexer<'src, Token<'src>>) -> Option<YarnBox<'src, str>> {
    let slice = lexer.slice();
    let content = slice.strip_prefix("\"")?.strip_suffix("\"")?;
    Some(YarnBox::new(content))
}

fn str_to_yarn<'src>(lexer: &mut Lexer<'src, Token<'src>>) -> YarnBox<'src, str> {
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
        "#;
        let lexer = Token::lexer(source);
        let tokens = lexer.into_iter().map(Result::unwrap).collect::<Vec<_>>();
        dbg!(tokens);
        panic!();
    }
}
