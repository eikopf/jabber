//! Rough AST structures for parsing (without source locations).

/// An individual _item_ (AKA entity or symbol).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Item {
    access_spec: Option<AccessSpec>,
    decl: Decl,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AccessSpec {
    Pub,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Mod(ModDecl),
    Import(ImportDecl),
    Enum(EnumDecl),
    Record(RecordDecl),
    Sig(SigDecl),
    Fn(FnDecl),
    Const(ConstDecl),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModDecl {
    ident: Ident,
    contents: Option<Box<[Item]>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportDecl {
    item: Name,
    alias: Option<Ident>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EnumDecl {
    name: Name,
    generic_params: Option<GenericParams>,
    variants: Box<[(Ident, Box<[Ty]>)]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordDecl {
    name: Name,
    generic_params: Option<GenericParams>,
    fields: Box<[(Ident, Ty)]>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SigDecl {
    ident: Ident,
    generic_params: Option<GenericParams>,
    ty: (Ty, Ty),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnDecl {
    name: Name,
    generic_params: Option<GenericParams>,
    params: Box<[Param]>,
    return_type: Option<Ty>,
    bounds: Box<[(Name, GenericParams)]>,
    body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstDecl {
    ident: Ident,
    ty: Ty,
    body: Expr,
}

/// An expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Block(Box<BlockExpr>),
    Match(Box<MatchExpr>),
    Ite(Box<IfThenElseExpr>),
    Call(Box<CallExpr>),
    Op(Box<OpExpr>),
    Literal(Box<Literal>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockExpr {
    statements: Box<[Stmt]>,
    result: Option<Expr>,
}

/// A statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Let(Pattern, Expr),
    Expr(Expr),
}

/// A structural pattern matching expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchExpr {
    scrutinee: Expr,
    arms: Box<[MatchArm]>,
}

/// An individual arm in a `match` expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatchArm {
    pattern: Pattern,
    body: Expr,
    guard: Option<Expr>,
}

/// A pattern, used in destructuring assignment
/// and structural pattern matching expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    /// The `_` (wildcard) pattern, which
    /// matches everything.
    Wildcard,
    /// The `..` (rest) pattern, which expands to
    /// "fill empty space" in variable length
    /// patterns.
    Rest,
    /// A literal value, matched by structural equality.
    ///
    /// [See also this related Rust RFC.](https://github.com/rust-lang/rfcs/blob/master/text/1445-restrict-constants-in-patterns.md)
    Literal(AtomicLiteral),
    /// A list of patterns matching against tuple values.
    ///
    /// This is a more permissive structure than necessary,
    /// since we require a tuple to have at least two elements.
    Tuple(Box<[Self]>),
    /// A list of patterns matching against lists with
    /// specific lengths. This _does not_ include the
    /// empty list, which is treated as a literal patten.
    List(Box<[Self]>),
    /// A combined _head_ and _tail_ pattern for generalised
    /// matching against sequences (like lists and strings).
    Cons(Box<Self>, Box<Self>),
    /// A destructured enum variant, matching only against a
    /// single enum variant of a single enum type.
    Enum(Name, Box<[Self]>),
    /// A destructured record pattern, matching only against
    /// the record type given as the name in the pattern.
    Record(Name, Box<[(Ident, Self)]>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IfThenElseExpr {
    cond: Expr,
    true_expr: Expr,
    false_expr: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallExpr {
    receiver: Expr,
    args: Option<Box<[Expr]>>,
}

/// An operator expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OpExpr {
    Prefix(PrefixOp, Box<Expr>),
    Infix(Box<Expr>, InfixOp, Box<Expr>),
    Postfix(Box<Expr>, PostfixOp),
}

/// A prefix operator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrefixOp {
    Bang,
    Dash,
    Tilde,
}

/// An infix operator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InfixOp {
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*` (the asterisk)
    Star,
    /// `/` (the forward slash)
    Slash,
    /// `%`
    Percent,
    /// `^` (the circumflex)
    Hat,
    /// `<<`
    LShift,
    /// `>>`
    RShift,
    /// `~`
    Tilde,
    /// `&` (the ampersand)
    Amp,
    /// `|` (the pipe _character_, not the pipe operator)
    Bar,
    /// `==`
    EqEq,
    /// `!=`
    BangEq,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `<=`
    Le,
    /// `>=`
    Ge,
    /// `<=>` (the ternary comparison operator)
    Cmp,
    /// `|>` (the pipe digraph)
    Pipe,
    /// `$` (the function application operator)
    Dollar,
    /// `.` (the function composition operator)
    Dot,
    /// `>>=` (the monadic-do operator)
    Bind,
    /// `::` (the _cons_ operator)
    Cons,
    /// `++` (the appending operator)
    PlusPlus,
}

/// A postfix operator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PostfixOp {
    Bang,
    Hook,
    Index(Expr),
}

/// A literal value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    Atom(AtomicLiteral),
    List(Box<[Expr]>),
    Record(RecordLiteral),
    Func(FuncLiteral),
}

/// A terminal literal, in the sense that it
/// cannot contain further literal values.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtomicLiteral {
    True,
    False,
    Unit,
    Name(Name),
    Char(char),
    String(Box<str>),
    Num(NumLiteral),
}

/// A numeric literal value.
///
/// Notice that this type admits some obviously
/// malformed numeric literals -- e.g. `3.14i32`.
/// However, parsing these literals as valid allows
/// us to later produce nicer error messages that
/// explain *why* such a literal value is malformed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumLiteral {
    pub digits: NumLiteralDigits,
    pub suffix: Option<PrimNum>,
}

/// The digits in a [`NumLiteral`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NumLiteralDigits {
    /// A purely integral digit sequence, i.e. without a decimal point.
    Int(u64),
    /// A purely integral digit sequence with a trailing decimal point.
    IntDot(u64),
    /// A purely fractional digit sequence, i.e. with a leading decimal point.
    Frac(u64),
    /// A digit sequence with both integral and fractional components.
    Real { int: u64, frac: u64 },
}

/// A literal record value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordLiteral {
    /// The name of the record type.
    pub name: Name,
    /// The field assignments.
    pub fields: Box<[(Ident, Expr)]>,
    /// The optional default source for otherwise-omitted
    /// field assignments.
    pub source: Option<Expr>,
}

/// A function literal (i.e. an anonymous function, or lambda expression).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuncLiteral {
    pub params: Box<[Param]>,
    pub body: Expr,
}

/// A function parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Param {
    Plain(Pattern),
    Typed(Pattern, Ty),
}

/// A type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ty {
    Prim(PrimTy),
    Name(Name, Option<GenericParams>),
    Func(Box<Ty>, Box<Ty>),
    Tuple(Box<[Ty]>),
}

/// A list of generic parameters and assignments.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericParams {
    pub params: Box<[Ty]>,
    pub fundeps: Option<Box<[Ty]>>,
}

/// A primitive concrete type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrimTy {
    Bottom,
    Unit,
    Bool,
    Char,
    String,
    Int(PrimInt),
    Float(PrimFloat),
}

/// A primitive numeric type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrimNum {
    Int(PrimInt),
    Float(PrimFloat),
}

/// A primitive integer type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrimInt {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
}

/// A primitive floating-point type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrimFloat {
    F32,
    F64,
}

/// An identifier parsed from source code.
pub type Ident = Box<str>;
/// A possibly-qualified name consisting of identifiers.
pub type Name = Box<[Ident]>;
