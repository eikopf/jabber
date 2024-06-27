//! Rough AST structures for parsing (without source locations).

/// The type corresponding to the `START`
/// symbol in the formal grammar.
pub type Start = Box<[Item]>;

/// An individual _item_ (AKA entity or symbol).
pub struct Item {
    access_spec: Option<AccessSpec>,
    decl: Decl,
}

pub enum AccessSpec {
    Pub,
}

pub enum Decl {
    Mod(ModDecl),
    Import(ImportDecl),
    Enum(EnumDecl),
    Record(RecordDecl),
    Sig(SigDecl),
    Fn(FnDecl),
    Const(ConstDecl),
}

pub struct ModDecl {
    ident: Ident,
    contents: Option<Box<[Item]>>,
}

pub struct ImportDecl {
    item: Name,
    alias: Option<Ident>,
}

pub struct EnumDecl {
    name: Name,
    generic_params: Option<GenericParams>,
    variants: Box<[(Ident, Box<[Ty]>)]>,
}

pub struct RecordDecl {
    name: Name,
    generic_params: Option<GenericParams>,
    fields: Box<[(Ident, Ty)]>,
}

pub struct SigDecl {
    ident: Ident,
    generic_params: Option<GenericParams>,
    ty: (Ty, Ty),
}

pub struct FnDecl {
    name: Name,
    generic_params: Option<GenericParams>,
    params: Box<[Param]>,
    return_type: Option<Ty>,
    bounds: Box<[(Name, GenericParams)]>,
    body: Expr,
}

pub struct ConstDecl {
    ident: Ident,
    ty: Ty,
    body: Expr,
}

/// An expression.
pub enum Expr {
    Block(Box<BlockExpr>),
    Match(Box<MatchExpr>),
    Ite(Box<IfThenElseExpr>),
    Call(Box<CallExpr>),
    Op(Box<OpExpr>),
    Literal(Box<Literal>),
}

pub struct BlockExpr {
    statements: Box<[Stmt]>,
    result: Option<Expr>,
}

/// A statement.
pub enum Stmt {
    Let(Pattern, Expr),
    Expr(Expr),
}

/// A structural pattern matching expression.
pub struct MatchExpr {
    scrutinee: Expr,
    arms: Box<[MatchArm]>,
}

/// An individual arm in a `match` expression.
pub struct MatchArm {
    pattern: Pattern,
    body: Expr,
    guard: Option<Expr>,
}

/// A pattern, used in destructuring assignment
/// and structural pattern matching expressions.
pub enum Pattern {
    /// The `_` (wildcard) pattern, which
    /// matches everything.
    Wildcard,
    /// The `..` (rest) pattern, which expands to
    /// "fill empty space" in variable length
    /// patterns.
    Rest,
    /// An identifier which may bind anything.
    Ident(Ident),
    /// A literal value, matched by structural equality.
    ///
    /// [See also this related Rust RFC.](https://github.com/rust-lang/rfcs/blob/master/text/1445-restrict-constants-in-patterns.md)
    Literal(Literal),
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

pub struct IfThenElseExpr {
    cond: Expr,
    true_expr: Expr,
    false_expr: Expr,
}

pub struct CallExpr {
    receiver: Expr,
    args: Option<Box<[Expr]>>,
}

/// An operator expression.
pub enum OpExpr {
    Prefix(PrefixOp, Box<Expr>),
    Infix(Box<Expr>, InfixOp, Box<Expr>),
    Postfix(Box<Expr>, PostfixOp),
}

/// A prefix operator.
pub enum PrefixOp {
    Bang,
    Dash,
    Tilde,
}

/// An infix operator.
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
pub enum PostfixOp {
    Bang,
    Hook,
    Dot(Ident),
    Index(Expr),
}

/// A literal value.
pub enum Literal {
    True,
    False,
    Unit,
    Name(Name),
    Char(char),
    String(Box<str>),
    Int(IntLiteral),
    Float(FloatLiteral),
    List(Box<[Expr]>),
    Record(RecordLiteral),
    Func(FuncLiteral),
}

/// A literal integer value.
pub struct IntLiteral {
    digits: usize,
    suffix: Option<PrimInt>,
}

/// A literal floating-point value.
pub struct FloatLiteral {
    int_digits: usize,
    frac_digits: usize,
    suffix: Option<PrimFloat>,
}

/// A literal record value.
pub struct RecordLiteral {
    /// The name of the record type.
    name: Name,
    /// The field assignments.
    fields: Box<[(Ident, Expr)]>,
    /// The optional default source for otherwise-omitted
    /// field assignments.
    source: Option<Expr>,
}

/// A function literal (i.e. an anonymous function, or lambda expression).
pub struct FuncLiteral {
    params: Box<[Param]>,
    body: Expr,
}

/// A function parameter.
pub enum Param {
    Plain(Ident),
    Typed(Ident, Ty),
}

/// A type.
pub enum Ty {
    Prim(Prim),
    Name(Name, Option<GenericParams>),
    Func(Box<Ty>, Box<Ty>),
    Pair(Box<Ty>, Box<Ty>),
}

/// A list of generic parameters and assignments.
pub struct GenericParams {
    params: Box<[Ty]>,
    fundeps: Option<Box<[Ty]>>,
}

/// A primitive concrete type.
pub enum Prim {
    Bottom,
    Unit,
    Bool,
    Char,
    String,
    Int(PrimInt),
    Float(PrimFloat),
}

/// A primitive integer type.
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
pub enum PrimFloat {
    F32,
    F64,
}

/// An identifier parsed from source code.
pub type Ident = Box<str>;
/// A possibly-qualified name consisting of identifiers.
pub type Name = Box<[Ident]>;
