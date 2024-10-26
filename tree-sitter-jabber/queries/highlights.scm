;; identifiers

(ident) @variable

(field_expr
  field: (ident) @property)

(primitive_type) @type.builtin

;; SCREAMCASE names with more than one character are assumed to be constants
((ident) @constant
  (#match? @constant "^[A-Z][A-Z]+$"))

;; modules
(mod_decl name: (ident) @module)

;; type decls
(type_decl
  name: (ident) @type.definition)

(type_alias_decl
  name: (ident) @type.definition
  type: (_) @type)

(extern_type_decl
  name: (ident) @type.definition)

(type_constructor
  name: (ident) @constructor)

(record_field
  name: (ident) @variable.member)

;; functions
(fn_decl name: (ident) @function)
(extern_fn_decl name: (ident) @function)

;; parameters
(parameter type: (_) @type)

;; const decls
(const_decl name: (ident) @constant)

;; attributes
"@" @punctuation.special

;; record literals

(record_expr
  name: (ident) @constructor)

(record_expr
  name: (path name: (ident) @constructor))

(record_expr_field
  name: (ident) @variable.member
  value: (_))

;; field expressions
(field_expr field: (_) @variable.member)
(tuple_field) @number

;; function and constructor calls
(call_expr callee:
  (ident) @function.call
  (#not-match? @function.call "^[A-Z]"))

(call_expr
  callee: (path name: (ident) @function.call)
  (#not-match? @function.call "^[A-Z]"))

(call_expr callee:
  (ident) @constructor
  (#match? @constructor "^[A-Z]"))

(call_expr
  callee: (path name: (ident) @constructor)
  (#match? @constructor "^[A-Z]"))

;; blocks
(let_stmt type: (_) @type)

;; types
"->" @punctuation.delimiter

(primitive_type) @type.builtin

(parenthesized_type
  (_) @type)

(fn_type
  domain: (_) @type
  codomain: (_) @type)

(fn_type_args      (_) @type)
(tuple_type        (_) @type)
(generic_type_args (_) @type)

(generic_type
  name: (ident) @type)

(generic_type
  name: (path name: (ident) @type))

;; pattern
"::" @constructor
(wildcard_pattern) @punctuation.delimiter

;; keywords

[
 "as"
 "const"
 "let"
 "mod"
 (super)
 (self)
 (package)
 ] @keyword

[
 "alias"
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

".." @punctuation.special

"(" @punctuation.bracket
")" @punctuation.bracket
"[" @punctuation.bracket
"]" @punctuation.bracket
"{" @punctuation.bracket
"}" @punctuation.bracket

"." @punctuation.delimiter
"," @punctuation.delimiter
":" @punctuation.delimiter
";" @punctuation.delimiter
"|" @punctuation.delimiter

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
