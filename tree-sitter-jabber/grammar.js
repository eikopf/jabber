/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

/**
 *  @param {RuleOrLiteral} rule
 */
const comma_list2 = (rule) => seq(rule, repeat1(seq(",", rule)), optional(","));

/**
 *  @param {RuleOrLiteral} rule
 */
const comma_list1 = (rule) => seq(rule, repeat(seq(",", rule)), optional(","));

/**
 *  @param {RuleOrLiteral} rule
 */
const comma_list0 = (rule) => optional(comma_list1(rule));

const PREC = {
  call: 16,
  field: 15,
  prefix: 13,
  pow: 12,
  mul: 11,
  add: 10,
  concat: 10,
  cons: 10,
  cmp: 9,
  pipe_left: 8,
  pipe_right: 7,
  lazy_and: 6,
  lazy_or: 5,
  update: 2,
  lambda: 0,
};

module.exports = grammar({
  name: "jabber",

  extras: ($) => [/\s/, $.comment],

  supertypes: ($) => [
    $._decl,
    $._expr,
    $._name,
    $._pattern,
    $._type_expr,
    $._literal_expr,
    $._attribute_argument,
  ],

  word: ($) => $.ident,

  // these are LR(1) conflicts --- places where the parser needs more than one
  // token of lookahead to parse the language correctly
  conflicts: ($) => [
    [$._expr, $._pattern],
    [$._expr, $._name],
    [$.list_expr, $.list_pattern],
    [$.record_expr, $.record_pattern],
    [$.record_expr_field, $.record_pattern_field],
  ],

  rules: {
    // start symbol
    source_file: ($) =>
      seq(
        optional(field("shebang", $.shebang)),
        optional(field("module_comment", $.module_comments)),
        field("declaration", repeat($.declaration)),
      ),

    shebang: (_) => /#![^\n]*/,

    /// DECLARATIONS

    access_spec: (_) => "pub",

    declaration: ($) =>
      seq(
        optional(field("docs", $.doc_comments)),
        optional(field("attributes", $.attributes)),
        optional(field("visibility", $.access_spec)),
        field("body", $._decl),
      ),

    _decl: ($) =>
      choice(
        $.mod_decl,
        $.use_decl,
        $.type_decl,
        $.type_alias_decl,
        $.extern_type_decl,
        $.fn_decl,
        $.extern_fn_decl,
        $.const_decl,
      ),

    mod_decl: ($) => seq("mod", field("name", $.ident)),

    use_decl: ($) => seq("use", field("item", $._use_item)),

    _use_item: ($) => choice($._name, $.alias_item, $.tree_item),

    alias_item: ($) =>
      seq(field("item", $._name), "as", field("alias", $.ident)),

    tree_item: ($) =>
      seq(
        optional(seq(field("root", $._name), ".")),
        field("items", $.tree_item_children),
      ),

    tree_item_children: ($) => seq("{", comma_list0($._use_item), "}"),

    extern_type_decl: ($) =>
      seq(
        "extern",
        "type",
        field("name", $.ident),
        optional(field("params", $.generic_params)),
      ),

    type_alias_decl: ($) =>
      seq(
        "type",
        "alias",
        field("name", $.ident),
        optional(field("params", $.generic_params)),
        "=",
        field("type", $._type_expr),
      ),

    type_decl: ($) =>
      seq(
        optional($.opaque),
        "type",
        field("name", $.ident),
        optional(field("params", $.generic_params)),
        "=",
        field("constructors", $.type_constructors),
      ),

    opaque: (_) => "opaque",

    type_constructors: ($) =>
      seq(
        optional("|"),
        $.type_constructor,
        repeat(seq("|", $.type_constructor)),
      ),

    type_constructor: ($) =>
      seq(
        optional(field("attributes", $.attributes)),
        optional(field("docs", $.doc_comments)),
        field("name", $.ident),
        optional(field("payload", $._type_constructor_payload)),
      ),

    _type_constructor_payload: ($) => choice($.tuple_payload, $.record_payload),

    tuple_payload: ($) => seq("(", comma_list1($._type_expr), ")"),
    record_payload: ($) => seq("{", comma_list1($.record_field), "}"),

    record_field: ($) =>
      seq(
        optional(field("docs", $.doc_comments)),
        optional(field("attributes", $.attributes)),
        optional(field("mutable", $.mutable)),
        field("name", $.ident),
        ":",
        field("type", $._type_expr),
      ),

    mutable: (_) => "mutable",

    generic_params: ($) => seq("[", comma_list1($.ident), "]"),

    fn_decl: ($) =>
      seq(
        "fn",
        field("name", $.ident),
        field("parameters", $.parameters),
        optional(seq("->", field("return_type", $._type_expr))),
        choice(
          seq("=", field("eq_body", $._expr)),
          field("block_body", $.block),
        ),
      ),

    extern_fn_decl: ($) =>
      seq(
        "extern",
        "fn",
        field("name", $.ident),
        field("parameters", $.parameters),
        optional(seq("->", field("return_type", $._type_expr))),
      ),

    parameters: ($) => seq("(", comma_list0($.parameter), ")"),
    parameter: ($) =>
      prec.left(
        seq(
          field("pattern", $._pattern),
          optional(seq(":", field("type", $._type_expr))),
        ),
      ),

    const_decl: ($) =>
      seq(
        "const",
        field("name", $.ident),
        ":",
        field("type", $._type_expr),
        "=",
        field("value", $._expr),
      ),

    /// ATTRIBUTES

    attributes: ($) => repeat1($.attribute),
    attribute: ($) =>
      seq(
        "@",
        field("name", $._name),
        optional(field("arguments", $.attribute_arguments)),
      ),
    attribute_arguments: ($) =>
      seq("(", comma_list0($._attribute_argument), ")"),
    _attribute_argument: ($) => choice($._name, $._literal_expr),

    /// EXPRESSIONS

    _expr: ($) =>
      choice(
        $.ident,
        $.path,
        $._literal_expr,
        $.list_expr,
        $.tuple_expr,
        $.record_expr,
        $.field_expr,
        $.lambda_expr,
        $.call_expr,
        $.prefix_expr,
        $.binary_expr,
        $.match_expr,
        $.if_else_expr,
        $.block,
        $.parenthesized_expr,
      ),

    parenthesized_expr: ($) => prec(1, seq("(", field("inner", $._expr), ")")),

    _literal_expr: ($) =>
      choice(
        $.unit_literal,
        $.bool_literal_true,
        $.bool_literal_false,
        $.char_literal,
        $.string_literal,
        $.float_literal,
        $.bin_literal,
        $.oct_literal,
        $.dec_literal,
        $.hex_literal,
      ),

    list_expr: ($) => seq("[", comma_list0($._expr), "]"),
    tuple_expr: ($) => seq("(", comma_list2($._expr), ")"),

    record_expr: ($) =>
      seq(
        field("name", $._name),
        "{",
        optional(field("fields", $.record_expr_fields)),
        "}",
      ),

    record_expr_fields: ($) =>
      seq(
        $.record_expr_field,
        repeat(seq(",", $.record_expr_field)),
        optional(seq(",", $.record_update_base)),
        optional(","),
      ),

    record_expr_field: ($) =>
      seq(field("name", $.ident), optional(seq(":", field("value", $._expr)))),
    record_update_base: ($) => seq("..", $._expr),

    field_expr: ($) =>
      seq(
        field("item", $._expr),
        ".",
        field("field", choice($.ident, $.tuple_field)),
      ),
    tuple_field: (_) => /[0-9]+/,

    lambda_expr: ($) =>
      prec.right(
        PREC.lambda,
        seq(
          field("parameters", $._lambda_params),
          "->",
          field("body", $._expr),
        ),
      ),
    _lambda_params: ($) => choice($.ident, $.parameters),

    call_expr: ($) =>
      prec(
        PREC.call,
        seq(field("callee", $._expr), field("arguments", $.arguments)),
      ),

    arguments: ($) => seq("(", comma_list0($._expr), ")"),

    prefix_expr: ($) =>
      prec.right(
        PREC.prefix,
        seq(field("operator", $.prefix_operator), field("operand", $._expr)),
      ),

    binary_expr: ($) => {
      const table = [
        [prec.right, PREC.pow, choice("^", "^.")],
        [prec.right, PREC.pipe_left, "<|"],
        [prec.left, PREC.pipe_right, "|>"],
        [
          prec.left,
          PREC.cmp,
          choice("==", "!=", ">", ">.", "<", "<.", ">=", ">=.", "<=", "<=."),
        ],
        [prec.left, PREC.add, choice("+", "+.", "-", "-.")],
        [prec.left, PREC.mul, choice("*", "*.", "/", "/.", "%")],
        [prec.right, PREC.cons, "::"],
        [prec.right, PREC.concat, "++"],
        [prec.right, PREC.lazy_and, "&&"],
        [prec.right, PREC.lazy_or, "||"],
        [prec.right, PREC.update, choice(":=", "<-")],
      ];

      return choice(
        ...table.map(([fn, prec, op]) =>
          //@ts-ignore
          fn(
            prec,
            seq(
              field("lhs", $._expr),
              //@ts-ignore
              field("operator", alias(op, $.binary_operator)),
              field("rhs", $._expr),
            ),
          ),
        ),
      );
    },

    prefix_operator: (_) => choice("!", "-", "-.", "*"),

    binary_operator: (_) =>
      choice(
        "+", // infix int add
        "+.", // infix float add
        "-", // prefix int neg / infix int sub
        "-.", // prefix float neg / infix float sub
        "*", // infix float mul / prefix deref
        "*.", //inflix float mul
        "/", // infix int div
        "/.", // infix float div
        "^", // infix int pow
        "^.", // infix float pow
        "%", // infix rem
        "==", // infix eq
        "!=", // infix neq
        ">", // infix int gt
        ">.", // infix float gt
        "<", // infix int lt
        "<.", // infix float lt
        ">=", // infix int ge
        ">=.", // infix float ge
        "<=", // infix int le
        "<=.", // infix float le
        "|>", // infix pipe right
        "<|", // infix pipe left
        "::", // infix cons
        "++", // infix concat
        "||", // infix lazy or
        "&&", // infix lazy and
        "<-", // infix update mutable field
        ":=", // infix update ref
      ),

    match_expr: ($) =>
      seq("match", field("scrutinee", $._expr), field("arms", $.match_arms)),

    match_arms: ($) => seq("{", comma_list0($.match_arm), "}"),
    match_arm: ($) =>
      seq(
        field("pattern", $._pattern),
        optional(field("guard", $.guard_expr)),
        "=>",
        field("body", $._expr),
      ),
    guard_expr: ($) => seq("if", $._expr),

    if_else_expr: ($) =>
      seq(
        "if",
        field("condition", $._expr),
        field("consequence", $.block),
        field("alternative", optional($.else_clause)),
      ),

    else_clause: ($) => seq("else", field("body", $.block)),

    block: ($) =>
      seq("{", repeat($._stmt), optional(field("return_expr", $._expr)), "}"),

    _stmt: ($) => choice($.empty_stmt, $.expr_stmt, $.let_stmt),

    empty_stmt: (_) => ";",
    expr_stmt: ($) => seq($._expr, ";"),
    let_stmt: ($) =>
      seq(
        "let",
        field("pattern", $._pattern),
        optional(seq(":", field("type", $._type_expr))),
        "=",
        field("value", $._expr),
        ";",
      ),

    /// PATTERNS

    _pattern: ($) =>
      choice(
        $._name,
        $._literal_expr,
        $.wildcard_pattern,
        $.tuple_pattern,
        $.list_pattern,
        $.cons_pattern,
        $.tuple_constructor_pattern,
        $.record_pattern,
        $.parenthesized_pattern,
      ),

    wildcard_pattern: (_) => "_",

    tuple_pattern: ($) => seq("(", comma_list2($._pattern), ")"),

    list_pattern: ($) => seq("[", comma_list0($._pattern), "]"),

    cons_pattern: ($) =>
      prec.right(
        seq(field("head", $._pattern), "::", field("tail", $._pattern)),
      ),

    tuple_constructor_pattern: ($) =>
      seq(
        field("name", $._name),
        field("payload", $.tuple_constructor_pattern_payload),
      ),
    tuple_constructor_pattern_payload: ($) =>
      seq("(", comma_list1($._pattern), ")"),

    record_pattern: ($) =>
      seq(
        field("name", $._name),
        "{",
        optional(field("fields", $.record_pattern_fields)),
        "}",
      ),

    record_pattern_fields: ($) =>
      seq(
        $.record_pattern_field,
        repeat(seq(",", $.record_pattern_field)),
        optional(seq(",", $.rest_pattern)),
        optional(","),
      ),

    record_pattern_field: ($) =>
      seq(
        field("field", $.ident),
        optional(seq(":", field("pattern", $._pattern))),
      ),

    rest_pattern: (_) => "..",

    parenthesized_pattern: ($) =>
      prec(10, seq("(", field("inner", $._pattern), ")")),

    /// TYPES

    _type_expr: ($) =>
      choice(
        $._name,
        $.primitive_type,
        $.unit_type,
        $.tuple_type,
        $.parenthesized_type,
        $.generic_type,
        $.fn_type,
        $.inferred_type,
      ),

    primitive_type: (_) =>
      choice("!", "bool", "char", "string", "int", "float"),

    unit_type: (_) => seq("(", ")"),

    tuple_type: ($) => seq("(", comma_list2($._type_expr), ")"),
    parenthesized_type: ($) =>
      prec(1, seq("(", field("inner", $._type_expr), ")")),

    generic_type: ($) =>
      seq(field("name", $._name), field("arguments", $.generic_type_args)),
    generic_type_args: ($) => seq("[", comma_list1($._type_expr), "]"),

    fn_type: ($) =>
      prec.right(
        seq(
          field("domain", choice($.fn_type_args, $._type_expr)),
          "->",
          field("codomain", $._type_expr),
        ),
      ),

    // this rule takes precedence over tuple_type and parenthesized_type
    fn_type_args: ($) => prec(2, seq("(", comma_list1($._type_expr), ")")),

    inferred_type: (_) => "_",

    /// LITERALS

    unit_literal: (_) => seq("(", ")"),
    bool_literal_true: (_) => "true",
    bool_literal_false: (_) => "false",
    char_literal: (_) => /'(\\'|.|\\u\{[0-9a-fA-F]+\}|\\x\d+|\\.)'/,
    string_literal: (_) => /"(\\"|[^"\r])*"/,
    bin_literal: (_) => /0b[01_]*[01][01_]*/,
    oct_literal: (_) => /0o[0-7_]*[0-7][0-7_]*/,
    hex_literal: (_) => /0[xX][0-9a-fA-F_]*[0-9a-fA-F][0-9a-fA-F_]*/,
    dec_literal: (_) => /[0-9][0-9_]*/,
    float_literal: (_) =>
      /[0-9][0-9_]*((\.[0-9][0-9_]*)?[eE][\+\-]?[0-9][0-9_]*|\.[0-9][0-9_]*)/,

    /// IDENTIFIERS

    _name: ($) => choice($.package, $.self, $.super, $.path, $.ident),

    path: ($) => seq(field("root", $._name), ".", field("name", $.ident)),

    package: (_) => "package",
    self: (_) => "self",
    super: (_) => "super",

    ident: (_) => /(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*/,

    /// COMMENTS

    comment: ($) =>
      seq(
        "//",
        optional(
          field(
            "marker",
            choice($.module_doc_comment_marker, $.decl_doc_comment_marker),
          ),
        ),
        $._comment_body,
      ),

    module_comments: ($) => repeat1(seq("//!", $._comment_body)),
    doc_comments: ($) => repeat1(seq("///", $._comment_body)),

    module_doc_comment_marker: (_) => token.immediate(prec(2, "!")),
    decl_doc_comment_marker: (_) => token.immediate(prec(2, "/")),
    _comment_body: (_) => token.immediate(/[^\n]*/),
  },
});
