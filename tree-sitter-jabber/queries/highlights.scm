;; identifiers

(ident) @variable

(field_expr
  field: (ident) @property)

(primitive_type) @type.builtin

;; SCREAMCASE names are assumed to be constants
((ident) @constant
  (#match? @constant "[A-Z]+"))

;; PascalCase names have extra assumptions attached
((ident) @constructor
  (#match? @constructor "^[A-Z]"))

;; modules
(mod_decl name: (ident) @module)

;; enums
(enum_decl name: (ident) @type.definition)
(enum_variant
  name: (ident) @constructor)

;; structs
(struct_decl name: (ident) @type.definition)
(struct_field name: (ident) @variable.member)

;; functions
(fn_decl name: (ident) @function)
(extern_fn_decl name: (ident) @function)

;; const decls
(const_decl name: (ident) @constant)

;; attributes
"@" @punctuation.special

;; field expressions
(field_expr field: (_) @variable.member)
(tuple_field) @number

;; function calls
(call_expr callee:             (ident) @function.call)
(call_expr callee: (path name: (ident) @function.call))

;; types
"->" @punctuation.delimiter

;; keywords

[
 "as"
 "const"
 "let"
 "mod"
 ] @keyword

[
 "enum"
 "struct"
 "type"
 ] @keyword.type

"fn" @keyword.function

"use" @keyword.import

[
 "if"
 "else"
 "match"
 ] @keyword.conditional

"extern" @keyword.modifier
(access_spec) @keyword.modifier
(mutable) @keyword.modifier

;; operators
(binary_operator) @operator
(prefix_operator) @operator

;; punctuation

(generic_params
  "[" @punctuation.bracket
  "]" @punctuation.bracket)
(generic_type_args
  "[" @punctuation.bracket
  "]" @punctuation.bracket)

"(" @punctuation.bracket
")" @punctuation.bracket
"[" @punctuation.bracket
"]" @punctuation.bracket

"." @punctuation.delimiter
"," @punctuation.delimiter
":" @punctuation.delimiter
";" @punctuation.delimiter

;; literals
(bool_literal_true) @boolean
(bool_literal_false) @boolean

(char_literal) @character
(string_literal) @string

(bin_literal) @number
(oct_literal) @number
(dec_literal) @number
(hex_literal) @number
(float_literal) @number.float

;; comments
(shebang) @keyword.directive
(comment) @comment
(doc_comments) @comment.documentation
(module_comments) @comment.documentation
