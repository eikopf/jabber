//! Manual parser implementations for literal expressions.
//!
//! Parsers in this module assume that their inputs are well-formed with
//! respect to the grammar—e.g. a string literal may be malformed due to an
//! invalid escape character, but will *always* be correctly delimited by
//! double quotes.

use winnow::{
    ascii::escaped_transform,
    combinator::{
        alt, cut_err, delimited, dispatch, empty, fail, opt, preceded,
        separated_pair,
    },
    error::{ContextError, ErrMode, InputError, StrContext, StrContextValue},
    token::{any, one_of, take_till, take_while},
    PResult, Parser,
};

use crate::span::{Span, Spanned};

const BACKSLASH: char = '\\';
const SINGLE_QUOTE: char = '\'';
const DOUBLE_QUOTE: char = '"';
const UNDERSCORE: char = '_';

pub type CharLiteral = Literal<char, CharKind>;
pub type StringLiteral = Literal<String>;
pub type IntLiteral = Literal<u64, IntKind>;
pub type FloatLiteral = Literal<f64, FloatKind>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Literal<T, K = ()> {
    span: Span,
    kind: K,
    value: T,
}

impl<T, K> Literal<T, K> {
    #[inline(always)]
    pub fn value(&self) -> &T {
        &self.value
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CharKind {
    Literal,
    Escape,
    Ascii,
    Unicode,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntKind {
    Bin,
    Oct,
    Dec,
    Hex,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FloatKind {
    Plain,
    Exponent,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLiteralError {
    input: Spanned<String>,
    offset: usize,
    bad_escape_span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CharLiteralError {
    input: Spanned<String>,
    /// The offset of the start of the error in the input.
    offset: usize,
    // The top-level error message, which should ideally not include newlines.
    message: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntLiteralOverflowError {
    input: Spanned<String>,
    offset: usize,
}

pub fn parse_string_literal(
    Spanned { item: input, span }: Spanned<&str>,
) -> Result<StringLiteral, StringLiteralError> {
    let mut parser = delimited("\"", string_contents, "\"");

    match parser.parse(input) {
        Ok(value) => Ok(Literal {
            value,
            kind: (),
            span,
        }),
        Err(error) => {
            let input = span.with(String::from(input));
            let escape_span_start = span.start + error.offset() as u32;
            let bad_escape_span = Span {
                start: escape_span_start,
                end: escape_span_start + error.inner().input.len() as u32,
            };

            Err(StringLiteralError {
                input,
                offset: error.offset(),
                bad_escape_span,
            })
        }
    }
}

pub fn parse_char_literal(
    Spanned { item: input, span }: Spanned<&str>,
) -> Result<CharLiteral, CharLiteralError> {
    let mut parser = delimited("'", char_contents, "'");

    match parser.parse(input) {
        Ok((value, kind)) => Ok(Literal { span, value, kind }),
        Err(error) => {
            // HACK: this is placeholder for a better error impl (eventually).
            let raw_message = error.inner().to_string();

            let input = span.with(String::from(input));
            let offset = error.offset();
            let message = raw_message
                .split_once('\n')
                .map(|(lhs, _)| String::from(lhs))
                .unwrap_or(raw_message);

            Err(CharLiteralError {
                input,
                offset,
                message,
            })
        }
    }
}

pub fn parse_bin_int_literal(
    Spanned { item: input, span }: Spanned<&str>,
) -> Result<IntLiteral, IntLiteralOverflowError> {
    match preceded("0b", digits::<2>).parse(input) {
        Ok(value) => Ok(Literal {
            value,
            kind: IntKind::Bin,
            span,
        }),
        Err(error) => Err(IntLiteralOverflowError {
            input: span.with(String::from(input)),
            offset: error.offset(),
        }),
    }
}

pub fn parse_oct_int_literal(
    Spanned { item: input, span }: Spanned<&str>,
) -> Result<IntLiteral, IntLiteralOverflowError> {
    match preceded("0o", digits::<8>).parse(input) {
        Ok(value) => Ok(Literal {
            value,
            kind: IntKind::Oct,
            span,
        }),
        Err(error) => Err(IntLiteralOverflowError {
            input: span.with(String::from(input)),
            offset: error.offset(),
        }),
    }
}

pub fn parse_dec_int_literal(
    Spanned { item: input, span }: Spanned<&str>,
) -> Result<IntLiteral, IntLiteralOverflowError> {
    match digits::<10>.parse(input) {
        Ok(value) => Ok(Literal {
            value,
            kind: IntKind::Dec,
            span,
        }),
        Err(error) => Err(IntLiteralOverflowError {
            input: span.with(String::from(input)),
            offset: error.offset(),
        }),
    }
}

pub fn parse_hex_int_literal(
    Spanned { item: input, span }: Spanned<&str>,
) -> Result<IntLiteral, IntLiteralOverflowError> {
    match preceded(('0', one_of(['x', 'X'])), digits::<16>).parse(input) {
        Ok(value) => Ok(Literal {
            value,
            kind: IntKind::Hex,
            span,
        }),
        Err(error) => Err(IntLiteralOverflowError {
            input: span.with(String::from(input)),
            offset: error.offset(),
        }),
    }
}

pub fn parse_float_literal(
    Spanned { item: input, span }: Spanned<&str>,
) -> FloatLiteral {
    // for reasons i don't understand, the ordering of these parsers
    // within alt is loadbearing
    match alt((exponent_float, plain_float)).parse(input) {
        Ok((kind, value)) => Literal { value, kind, span },
        Err(error) => {
            dbg!(error);
            unreachable!()
        }
    }
}

fn string_contents<'s>(
    input: &mut &'s str,
) -> PResult<String, InputError<&'s str>> {
    escaped_transform(
        take_till(1.., |c| c == BACKSLASH || c == DOUBLE_QUOTE),
        BACKSLASH,
        alt((
            "\\".value("\\"), // BACKSLASH
            "\"".value("\""), // DOUBLE QUOTE
            "n".value("\n"),  // NEWLINE (LINE FEED)
            "r".value("\r"),  // CARRIAGE RETURN
            "t".value("\t"),  // HORIZONTAL TAB
            "0".value("\0"),  // ASCII NULL
        )),
    )
    .parse_next(input)
}

fn char_contents(input: &mut &str) -> PResult<(char, CharKind)> {
    alt((preceded(BACKSLASH, char_escape), single_char)).parse_next(input)
}

fn single_char(input: &mut &str) -> PResult<(char, CharKind)> {
    any.parse_next(input).map(|c| (c, CharKind::Literal))
}

fn char_escape(input: &mut &str) -> PResult<(char, CharKind)> {
    dispatch! {any;
        'u' => delimited('{', unicode_code_point, '}'),
        'x' => ascii_byte,
        '0' => empty.value('\0').map(|c| (c, CharKind::Escape)),
        'n' => empty.value('\n').map(|c| (c, CharKind::Escape)),
        'r' => empty.value('\r').map(|c| (c, CharKind::Escape)),
        't' => empty.value('\t').map(|c| (c, CharKind::Escape)),
        BACKSLASH => empty.value(BACKSLASH).map(|c| (c, CharKind::Escape)),
        SINGLE_QUOTE => empty.value(SINGLE_QUOTE).map(|c| (c, CharKind::Escape)),
        _ => fail,
    }
    .parse_next(input)
}

fn unicode_code_point(input: &mut &str) -> PResult<(char, CharKind)> {
    take_while(1..=6, |c: char| c.is_ascii_hexdigit())
        .verify_map(|digits| {
            // SAFETY: digits is a string of hexadecimal digits with a maximum
            // length of 6, so its max value is 0xFFFFFF < u32::MAX
            let codepoint =
                unsafe { u32::from_str_radix(digits, 16).unwrap_unchecked() };

            char::from_u32(codepoint).map(|c| (c, CharKind::Unicode))
        })
        .parse_next(input)
}

fn ascii_byte(input: &mut &str) -> PResult<(char, CharKind)> {
    cut_err((oct_digit, hex_digit))
        .parse_next(input)
        .map(|(oct, hex)| {
            // SAFETY: the parser functions guarantee the only possible values
            // for hex_digit and oct_digit are also valid hexadecimal and octal
            // digits respectively.
            let upper = unsafe { oct.to_digit(8).unwrap_unchecked() };
            let lower = unsafe { hex.to_digit(16).unwrap_unchecked() };

            // upper <= 0x7 and lower <= 0xF, so (upper << 4) + lower <= 0x7F
            let ascii_byte = ((upper << 4) + lower) as u8 as char;
            debug_assert!(ascii_byte.is_ascii());

            (ascii_byte, CharKind::Ascii)
        })
}

fn oct_digit(input: &mut &str) -> PResult<char> {
    any.verify(|c| ('0'..='7').contains(c))
        .context(StrContext::Label("octal digit"))
        .context(StrContext::Expected(StrContextValue::Description(
            "an octal digit in the range from 0 to 7 (inclusive)",
        )))
        .parse_next(input)
}

fn hex_digit(input: &mut &str) -> PResult<char> {
    any.verify(char::is_ascii_hexdigit)
        .context(StrContext::Label("hexadecimal digit"))
        .parse_next(input)
}

// NOTE: both the *_float parsers are farming out the work of converting to f64
// to f64's FromStr impl, since it's more accurate than what i can put together
// in an afternoon. this is obviously slower that implementing it manually
// (it literally involves an entire string allocation!), but for now it's good
// enough.

fn plain_float(input: &mut &str) -> PResult<(FloatKind, f64)> {
    separated_pair(digits::<10>, ".", digits::<10>)
        .parse_next(input)
        .map(|(int, frac)| {
            (
                FloatKind::Plain,
                format!("{}.{}", int, frac).parse::<f64>().unwrap(),
            )
        })
}

fn exponent_float(input: &mut &str) -> PResult<(FloatKind, f64)> {
    (
        digits::<10>,
        opt(preceded('.', digits::<10>)),
        one_of(['e', 'E']),
        opt(one_of(['+', '-'])),
        digits::<10>,
    )
        .parse_next(input)
        .map(|(int, frac, _, sign, power)| {
            (
                FloatKind::Exponent,
                format!(
                    "{}.{}e{}{}",
                    int,
                    frac.unwrap_or(0),
                    sign.unwrap_or('+'),
                    power
                )
                .parse::<f64>()
                .unwrap(),
            )
        })
}

/// Parses a well-formed integer literal of the given `RADIX`, yielding a `u64`
/// value. The only failure mode for this function is if the integer literal is
/// too large to fit into a `u64`.
fn digits<const RADIX: u32>(input: &mut &str) -> PResult<u64> {
    take_while(1.., |c: char| c == UNDERSCORE || c.is_digit(RADIX))
        .parse_next(input)
        .and_then(|s| {
            s.chars()
                .filter(|&c| c != UNDERSCORE)
                .try_fold(0u64, |sum, digit| {
                    let (shifted_sum, overflowed) =
                        sum.overflowing_mul((RADIX).into());

                    // SAFETY: the parser guarantees digit will be a valid
                    // digit with respect to RADIX
                    let digit = unsafe {
                        digit.to_digit(RADIX).unwrap_unchecked() as u64
                    };

                    shifted_sum.checked_add(digit).filter(|_| !overflowed)
                })
                .ok_or_else(|| ErrMode::Backtrack(ContextError::new()))
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn complete_strings() {
        let parse = |s| {
            parse_string_literal(Span::ZERO.with(s))
                .map(|Literal { value, .. }| value)
        };

        // "" --> ε
        assert_eq!(parse(r#""""#), Ok(String::from("")));

        // "hello, world!" --> hello, world!
        assert_eq!(
            parse(r#""hello, world!""#),
            Ok(String::from("hello, world!"))
        );

        // "\t" --> U+0009 (Character Tabulation)
        assert_eq!(parse(r#""\t""#), Ok(String::from("\u{0009}")));

        // bad escapes yield errors
        assert!(parse(r#""\e""#).is_err());
    }

    #[test]
    fn string_escapes() {
        let parse = |s| string_contents.parse(s);

        // empty string
        assert_eq!(parse(r#""#), Ok(String::from("")));

        // escaped backslash
        assert_eq!(parse(r#"\\"#), Ok(String::from("\\")));

        // escaped double quote
        assert_eq!(parse(r#"\""#), Ok(String::from("\"")));

        // newline
        assert_eq!(parse(r#"\n"#), Ok(String::from("\n")));

        // carriage return
        assert_eq!(parse(r#"\r"#), Ok(String::from("\r")));

        // horizontal tab
        assert_eq!(parse(r#"\t"#), Ok(String::from("\t")));

        // ascii null
        assert_eq!(parse(r#"\0"#), Ok(String::from("\0")));
    }

    #[test]
    fn complete_character_literals() {
        let parse = |s| {
            parse_char_literal(Span::ZERO.with(s))
                .map(|lit| (lit.value, lit.kind))
        };

        // DIRECT CHARACTER LITERALS
        assert_eq!(parse(r#"'a'"#), Ok(('a', CharKind::Literal)));
        assert_eq!(parse(r#"'ü'"#), Ok(('ü', CharKind::Literal)));
        assert_eq!(parse(r#"'¬'"#), Ok(('¬', CharKind::Literal)));
        assert_eq!(parse(r#"'睷'"#), Ok(('睷', CharKind::Literal))); // U+7777

        // SPECIAL ESCAPED CHARACTER LITERALS
        assert_eq!(parse(r#"'\t'"#), Ok(('\t', CharKind::Escape)));
        assert_eq!(parse(r#"'\n'"#), Ok(('\n', CharKind::Escape)));
        assert_eq!(parse(r#"'\r'"#), Ok(('\r', CharKind::Escape)));
        assert_eq!(parse(r#"'\0'"#), Ok(('\0', CharKind::Escape)));
        assert_eq!(parse(r#"'\\'"#), Ok(('\\', CharKind::Escape)));
        assert_eq!(parse(r#"'\''"#), Ok(('\'', CharKind::Escape)));

        // ASCII BYTE CHARACTER LITERALS
        assert_eq!(parse(r#"'\x00'"#), Ok(('\x00', CharKind::Ascii))); // MIN
        assert_eq!(parse(r#"'\x7F'"#), Ok(('\x7F', CharKind::Ascii))); // MAX
        assert!(parse(r#"'\x8F'"#).is_err()); // MAX + 1

        // UNICODE CODE POINT CHARACTER LITERALS
        assert_eq!(parse(r#"'\u{0}'"#), Ok(('\u{0}', CharKind::Unicode)));
        assert_eq!(parse(r#"'\u{7777}'"#), Ok(('\u{7777}', CharKind::Unicode)));
        assert!(parse(r#"'\u{}'"#).is_err()); // too short
        assert!(parse(r#"'\u{01234567}'"#).is_err()); // too long
        assert!(parse(r#"'\u{D800}'"#).is_err()); // not a scalar value
    }

    #[test]
    fn complete_binary_integer_literals() {
        let parse =
            |s| parse_bin_int_literal(Span::ZERO.with(s)).map(|lit| lit.value);

        assert_eq!(parse(r#"0b____0000____0000"#), Ok(0));
        assert_eq!(parse(r#"0b____0000____0011"#), Ok(0b11));
        assert_eq!(parse(r#"0b1011"#), Ok(0b1011));
        assert_eq!(parse(r#"0b__10____11__"#), Ok(0b1011));
    }

    #[test]
    fn complete_octal_integer_literals() {
        let parse =
            |s| parse_oct_int_literal(Span::ZERO.with(s)).map(|lit| lit.value);

        assert_eq!(parse(r#"0o00"#), Ok(0));
        assert_eq!(parse(r#"0o77"#), Ok(0o77));
        assert!(parse(r#"0o78"#).is_err());
    }

    #[test]
    fn complete_decimal_integer_literals() {
        let parse =
            |s| parse_dec_int_literal(Span::ZERO.with(s)).map(|lit| lit.value);

        assert_eq!(parse(r#"0"#), Ok(0));
        assert_eq!(parse(r#"00____00"#), Ok(0));
        assert_eq!(parse(r#"314159"#), Ok(314159));
        assert!(parse(r#"1234F"#).is_err());
    }

    #[test]
    fn complete_hexadecimal_integer_literals() {
        let parse =
            |s| parse_hex_int_literal(Span::ZERO.with(s)).map(|lit| lit.value);

        assert_eq!(parse(r#"0x000"#), Ok(0));
        assert_eq!(parse(r#"0xff"#), Ok(0xff));
        assert_eq!(parse(r#"0XFF"#), Ok(0xFF));
    }

    #[test]
    fn complete_float_literals() {
        let parse = |s| parse_float_literal(Span::ZERO.with(s)).value;

        assert_eq!(parse(r#"0.0"#), 0.0);
        assert_eq!(parse(r#"13.3333"#), 13.3333);
        assert_eq!(parse(r#"0.17e16"#), 0.17e16);
        assert_eq!(parse(r#"1E-30"#), 1E-30);
    }
}
