////////////// DOCUMENT METADATA

#set document(
  author: "Oliver Wooding <oliverwooding@icloud.com>",
  date: datetime.today(),
  title: "COC255 Final Report --- Oliver Wooding (F214180)",
)

// spellchecking in en-GB
#set text(lang: "en", region: "GB")

/////////////// PACKAGES

// for diagrams
#import "@preview/fletcher:0.5.2" as fletcher: diagram, node, edge

// for standard mathematical forms
#import "@preview/lemmify:0.1.8": *

#let (
  definition,
  theorem,
  lemma,
  corollary,
  remark,
  proposition,
  example,
  proof,
  rules: thm-rules,
) = default-theorems(
  "thm-group",
  lang: "en",
  thm-numbering: thm-numbering-linear,
)

#show: thm-rules

#let remark = remark.with(numbering: none)

// glossary
#import "@preview/glossarium:0.5.3": (
  make-glossary,
  register-glossary,
  print-glossary,
  gls,
  glspl,
  gls-short,
)
#show: make-glossary
#import "glossary.typ": entry-list
#register-glossary(entry-list)

/////////////// UTILITY FUNCTIONS

#let todo(note) = highlight(fill: red.lighten(40%), extent: 2pt)[TODO: #note]
#let note(note) = highlight(fill: blue.lighten(60%), extent: 2pt)[NOTE: #note]

// glossary helpers
#let short(term) = gls(term, display: gls-short(term))

// inline columnar layout that can be contrasted with the ordinary flow
#let shortcolumns(left, right, cols: (1fr, 1fr)) = grid(
  columns: cols,
  column-gutter: 8pt,
  inset: 2pt,
  left,
  grid.vline(stroke: gray),
  right
)

/////////////// GLOBAL STYLING RULES

/// FIGURES
#set figure(kind: "figure", supplement: "Figure")

/// TABLES
#set table(align: center + horizon)

/// CODE BLOCKS
#show raw: set text(font: "Berkeley Mono")
#set raw(syntaxes: "EBNF.sublime-syntax")
// note: EBNF syntax file derived from https://github.com/sanssecours/EBNF.tmbundle

/// LAYOUT
#set page(margin: (x: 3em, y: 3em))

/// HEADINGS
#let content_heading_numbering = "1.1"
#set heading(numbering: content_heading_numbering)
#show heading.where(level: 2): set text(size: 20pt)
#show heading.where(level: 3): set text(size: 18pt)

// this explicitly adds space between the number and body in a heading,
// since typst's default style makes this quite cramped
#show heading: it => {
  v(0pt)
  if it.numbering != none {
    numbering(it.numbering, ..counter(heading).get())
    h(11pt) // a little less than 1em seems good here, at least 10pt
  }
  it.body
  v(0pt)
}

/// QUOTES
#set quote(block: true)
#show quote: set pad(x: 5em)

/// TEXT
#set text(size: 14pt)

/// CITATIONS/REFERENCES
#set cite(style: "ieee")

////////////// COVER PAGE

#align(right)[
  #pad(x: 2em)[
    #set text(size: 14pt)
    #text("Computer Science and Mathematics BSc")

    24COC255

    F214180
  ]]

#v(5em)

#align(center)[
  #set text(size: 25pt, weight: "bold")
  Designing and Implementing a Functional Programming Language

  #v(0.5em)

  #set text(size: 18pt, weight: "regular")
  #smallcaps[by]

  #v(1em)

  Oliver Wooding
]

#v(14em)

#align(center)[
  #set text(size: 18pt, weight: "regular")
  Supervisor: Dr. Joel Day

  #v(1em)

  Department of Computer Science #linebreak()
  Loughborough University

  #v(1em)

  May 2025
]

#pagebreak()

#set par(justify: true)

/////////////// TABLE OF CONTENTS

// uncomment this line to split the TOC into two columns
#set page(columns: 2)

#show outline.entry: it => {
  set text(size: 15pt)
  it
}

#show outline.entry.where(level: 1): it => {
  v(1.5em, weak: true)
  set text(size: 20pt)
  show repeat: none // i hate this, but it does remove the dot padding
  strong(it)
}

#outline(
  title: text(size: 24pt)[Table of Contents],
  indent: auto,
  depth: 2,
)

#set page(columns: 1)

// manual page break to make the page number correct
#pagebreak()

/////////////// CONTENTS

// page numbering is enabled at this point to prevent page numbers appearing
// on any of the "pre-content" pages
#counter(page).update(1)
#set page(numbering: "1")
#set heading(supplement: "§")
#show heading.where(level: 1, numbering: content_heading_numbering): it => {
  set text(size: 24pt)
  let (n, ..) = counter(heading).get()
  [
    #pagebreak(weak: true)
    Chapter #n --- #it.body
    #v(8pt)
  ]
}

#set text(13pt)


= Introduction <chapter-introduction>

#quote(attribution: [Philip Wadler, 1998 @wadler-why-no-one-uses-functional-languages])[... I work at Bell Labs, where @c and @cpp were invented. Compared to users of @c, "no one" is a tolerably accurate count of the users of functional languages.]

== Functional Programming <section-intro-functional-programming>

A _functional programming language_ is a programming language generally designed to avoid mutable state. These languages often feature complex type systems that allow a programmer to eliminate invalid states and provide powerful #short("api")s, and they are often described as being _declarative:_ a programmer describes _what_ they want to happen instead of _how_ it should happen, with execution details left to the language's runtime.

The earliest functional language in the modern sense
#footnote[
  By some definitions, the first functional language was John McCarthy's @lisp @mccarthy-history-of-lisp, which was first described in the late 1950s. However in the modern sense of the term, @lisp and its descendants are generally not seen as functional programming languages, and so have not been included here.
]
was @ml @milner-how-ml-evolved, and its descendants—particularly @haskell and @ocaml—are still widely considered to be prototypical examples of functional languages. More recent languages like @elm and @idris2 still largely hold to the @ml syntax family, but introduce their own features and designs to fit with modern norms. Other languages like @gleam and @scala have worked to combine functional programming with better-known syntactic templates, drawing from @rust and @java respectively.

Though functional programming languages have always been less popular than their imperative cousins @wadler-why-no-one-uses-functional-languages, some features of functional programming have bled into more mainstream languages @khanfor-overview-of-practical-impacts-of-functional-programming: @rust and @swift have popularised typeclass-like systems, while the prevalence of @typescript over @javascript reflects the rising popularity of static typing.

== Compilers <section-intro-compilers>

A _compiler_ is a program that transforms data into some kind of artifact, which can usually be executed. While this might well describe virtually any program, the key property of a compiler is that it _preserves meaning:_ the semantics of the data—when viewed as source code—must be faithfully transferred to the artifact.

An _optimising_ compiler is one which exploits the semantics of a language to apply meaning-invariant transformations to obtain beneficial properties in the resulting artifact.

Sometimes a distinction is drawn between ordinary compilers and _transpilers_, where a transpiler is a compiler whose artifacts are programs in a primarily human-readable programming language. Programming language dialects are commonly implemented by transpilers, as is the case for @typescript (targeting @javascript) and @fennel (targeting @lua).

== Aims <section-intro-aims>

The aims of this project were as follows:

#let __aims_chapter_ref(chapter) = [#h(1fr) (discussed in #chapter) #h(15pt)]

+ To design a functional programming language called Jabber. #__aims_chapter_ref([@chapter-design])
+ To formally describe Jabber's type system. #__aims_chapter_ref([@chapter-formal-types])
+ To implement a compiler for Jabber. #__aims_chapter_ref([@chapter-impl])

A critical evaluation of these aims with respect to the final status of the project is given in @chapter-evaluation, and overall outcomes and future work are discussed in @chapter-conclusion.

#v(1fr)

#align(center)[
  #figure(
    caption: [An example Jabber program modelling a subset of the IMP language.],
    ```jabber
    use core.io.println
    use core.int.to_string as int_to_string

    type AExp =
      | Int(int)            // integer
      | Add(AExp, AExp)     // +
      | Sub(AExp, AExp)     // - (with floor at 0)
      | Mul(AExp, AExp)     // *

    type BExp =
      | Atom(bool)          // true or false
      | Not(BExp)           // boolean NOT
      | And(BExp, BExp)     // boolean AND
      | Eq(AExp, AExp)      // integer equality
      | Le(AExp, AExp)      // less than or equal

    fn eval_aexp(expr: AExp) -> int = match expr {
      AExp.Int(i)    => i,
      AExp.Add(l, r) => eval_aexp(l) + eval_aexp(r),
      AExp.Mul(l, r) => eval_aexp(l) * eval_aexp(r),
      AExp.Sub(l, r) => {
        let l = eval_aexp(l);
        let r = eval_aexp(r);
        if l < r { 0 } else { l - r }
      },
    }

    fn eval_bexp(expr: BExp) -> bool = match expr {
      BExp.Atom(b)   => b,
      BExp.Not(expr) => !eval_bexp(expr),
      BExp.And(l, r) => eval_bexp(l) && eval_bexp(r),
      BExp.Eq(l, r)  => eval_aexp(l) == eval_aexp(r),
      BExp.Le(l, r)  => eval_aexp(l) <= eval_aexp(r),
    }

    fn main() {
      let lhs = AExp.Mul(AExp.Int(3), AExp.Int(2)); //  3 * 2
      let rhs = AExp.Sub(AExp.Int(5), AExp.Int(6)); // ⌊5 - 6⌋
      let sum = AExp.Add(lhs, rhs);                 // (3 * 2) + (⌊5 - 6⌋)
      eval_aexp(sum) |> int_to_string |> println    // prints 6
    }
    ```,
  )
]

#v(1em)

= Design <chapter-design>

// the point of having this quote here is to repeat it in the last chapter, so
// it can match the first and last stanzas of the poem

#quote(attribution: [_Jabberwocky_ by Lewis Carroll, 1871])[
  'Twas brillig, and the slithy toves\
  Did gyre and gimble in the wabe:\
  All mimsy were the borogoves,\
  And the mome raths outgrabe.
]

== Principles <section-design-principles>

Most languages espouse some driving principles and use them to motivate their design decisions; the most famous example is probably _The Zen of @python _ @the-zen-of-python. @julia was squarely aimed at meeting the requirements of scientific applications @julia-1-11-documentation, whereas much of the official material about @rust emphasises accessibility and control @the-rust-language-paper, @the-rust-programming-language.

Instead of real-world applications,
#footnote[This is arguably the manner in which Jabber _most_ qualifies as a functional language.]
Jabber looks to other functional languages to find _consensus_. Among dozens of major languages and over decades of work, norms and expectations have formed, and a broad variety of potential design decisions have been considered, explored, and abandoned. What remains is precisely the consensus position: those designs and ideas which have persisted based on their merit and utility.

In this regard, Jabber is interested more in stopping to look around at its peers and ancestors than it is in trying to carve some bold new direction. It is an artifact of its time and place, and will pursue novel solutions only where consensus is absent.

== Lexical Structure <section-design-lexical-structure>

The _lexical structure_ of a language is the system of rules governing how the raw contents of a source file should be treated—usually by the _lexer_—before it is parsed. More formally, the lexical structure can be viewed as defining a regular language of _tokens_ that the full grammar of the language may use as terminal rules.

Jabber's lexical structure presumes that all string data is encoded in @utf8 and takes the term _character_ to mean @unicode-scalar-value as defined in the @unicode Standard @unicode-standard-16, and unless otherwise specified the term _whitespace_ to mean sequences of characters that have the `Pattern_White_Space` Unicode property. It is assumed that the character sequence `U+000D` (CR) followed immediately by `U+000A` (LF) never occurs; in practice the compiler replaces such sequences with a single `U+000A` (LF) character.

#let __ls_comment_grammar = {
  ```ebnf
  comment = marker, body ;
  body = { ? any character except U+000A (LF) ? } ;
  marker = '//'   (* line comment *)
         | '//!'  (* module comment *)
         | '///'  (* documentation comment *)
         ;
  ```
}

#figure(
  caption: [The EBNF grammar for comments.],
  __ls_comment_grammar,
) <figure-comment-ebnf-grammar>

Most tokens are defined by a specific character sequence—this is how keywords and operators are defined, for example—so the remainder of this section will only consider the token families defined by regular grammars: _comments_, _identifiers_, and _literals_.

Comment tokens (@figure-comment-ebnf-grammar) are the simplest nontrivial tokens, in that they are recognised by the small regular expression `\/\/[^\n]*`. The grammar distinguishes between three `marker` options to preserve information about the intended function of the comment.

#let __ls_ident_grammar = {
  ```ebnf
  identifier = prefix, suffix ;
  prefix = underscore, { underscore }, (alpha | num) | alpha ;
  suffix = { underscore | alpha | num } ;

  alpha       = lower alpha | upper alpha ;
  lower alpha = ? characters in the range U+0041–U+005A (inclusive) ? ;
  upper alpha = ? characters in the range U+0061—U+007A (inclusive) ? ;
  num         = ? characters in the range U+0030—U+0039 (inclusive) ? ;
  underscore  = ? U+005F (Low Line) ? ;
  ```
}

#figure(
  caption: [The EBNF grammar for identifiers.],
  __ls_ident_grammar,
) <figure-ident-ebnf-grammar>

The grammar for @identifier tokens (@figure-ident-ebnf-grammar) is carefully designed to allow the usual range of `snake_cased` alphanumeric names while explicitly disallowing @identifier:pl that consist entirely of at least two `U+005F` characters; the motivation here is to avoid the confusion caused when users are made to differentiate @identifier:pl like `___` and `____`.

#let __ls_char_literal_grammar = {
  ```ebnf
  character literal = quote content quote ;
  content = single character | '\', escape ;

  escape = quote                                (* literal single quote *)
         | double quote                         (* literal double quote *)
         | 'r'                                  (* literal carriage return *)
         | 'n'                                  (* literal newline *)
         | 't'                                  (* literal horizontal tab *)
         | '0'                                  (* literal null character *)
         | '\'                                  (* literal backslash *)
         | 'u{', hex digit, { hex digit }, '}'  (* unicode code point *)
         | 'x', oct digit, hex digit            (* ascii character *)
         ;

  quote        = ? U+0027 (Apostrophe)     ? ;
  double quote = ? U+0022 (Quotation Mark) ? ;

  single character =
    ? any character other than U+0027, U+005C, U+000A, U+000D, or U+0009 ? ;
  ```
}

#figure(
  caption: [The EBNF grammar for character literals.],
  __ls_char_literal_grammar,
) <figure-character-literal-ebnf-grammar>

Character literal tokens (@figure-character-literal-ebnf-grammar) are more complicated than one might expect, but this arguably reflects the fact that _characters_ themselves are quite complex.
#footnote[As an example, this grammar is not _strictly_ correct: the character literal `'\u{DAA0}'` is a valid character literal but an *invalid* character, since U+DAA0 is not a @unicode-scalar-value and lies within the High Surrogates character block.]
This grammar provides syntax for direct character literals (e.g. `'a'`, `'ø'`, `'瘲'`), escaped non-textual characters (e.g. `'\r'`, `'\t'`, `'\0'`), ASCII byte character literals (e.g. `'\x7A'`, `'\x00'`) and @unicode-code-point literals (e.g. `'\u{0039}'`, `'\u{0}'`). This portion of the lexical structure draws heavily from #gls("rust", display: "Rust's") character syntax, and in fact the only substantial differences between them are related to @rust\-specific esoterica @the-rust-reference[§2.6].

#let __ls_string_literal_grammar = {
  ```ebnf
  string literal = double quote, { string element }, double quote ;
  string element = '\', double quote
                 | ? any character other than U+000D or U+0022 ?
                 ;
  ```
}

#figure(
  caption: [The EBNF grammar for string literals.],
  __ls_string_literal_grammar,
) <figure-string-literal-ebnf-grammar>

By contrast, the grammar for string literal tokens (@figure-string-literal-ebnf-grammar) is much simpler and just admits any double-quote-delimited sequence of characters—with special affordances made for escaped double quotes and U+000D (CR).

#let __ls_integer_literal_grammar = {
  ```ebnf
  int literal = bin literal     (* base 2 *)
              | oct literal     (* base 8 *)
              | dec literal     (* base 10 *)
              | hex literal     (* base 16 *)
              ;

  bin literal = bin prefix, {bin digit | '_'}, bin digit, {bin digit | '_'} ;
  oct literal = oct prefix, {oct digit | '_'}, oct digit, {oct digit | '_'} ;
  dec literal =                                dec digit, {dec digit | '_'} ;
  hex literal = hex prefix, {hex digit | '_'}, hex digit, {hex digit | '_'} ;

  bin prefix = '0b' ;
  oct prefix = '0o' ;
  hex prefix = '0x' | '0X' ;

  bin digit = '0' | '1' ;
  oct digit = bin digit | '2' | '3' | '4' | '5' | '6' | '7' ;
  dec digit = oct digit | '8' | '9' ;
  hex digit = dec digit
            | 'a' | 'b' | 'c' | 'd' | 'e' | 'f'
            | 'A' | 'B' | 'C' | 'D' | 'E' | 'F'
            ;
  ```
}

#figure(
  caption: [The EBNF grammar for integer literals.],
  __ls_integer_literal_grammar,
) <figure-integer-literal-ebnf-grammar>

Integer literal tokens (@figure-integer-literal-ebnf-grammar) are defined quite simply, though they still allow for binary, octal, decimal, and hexadecimal literals. Underscores (U+005F) can be arbitrarily used to demarcate digit groupings, so the tokens `0b___0___` and `0b0` are semantically equivalent. Notice that integer literals do not have a leading sign character; a code fragment like `-17` consists of two distinct tokens for the `-` character and the literal `17`.

#let __ls_float_literal_grammar = {
  ```ebnf
  float literal = dec literal,  '.', dec literal
                | dec literal, ['.', dec literal], exponent
                ;

  exponent = ('e' | 'E'), ['+' | '-'], dec literal ;
  ```
}

#figure(
  caption: [The EBNF grammar for floating point literals.],
  __ls_float_literal_grammar,
) <figure-float-literal-ebnf-grammar>

Floating point literal tokens (@figure-float-literal-ebnf-grammar) consist of a leading integral prefix, and then are terminated either by a fractional component or a signed exponent. Like integer literals, they do not have a leading sign character.

== Syntax <section-design-syntax>
//See @appendix-formal-grammar for the complete formal grammar.

Jabber's syntax can be broadly broken into four major areas:

+ _Declarations_
+ _Expressions_
+ _Patterns_
+ _Types_

=== Declarations <subsection-design-syntax-declarations>

Declarations are the primary subdivision within the grammar; all Jabber source files are fundamentally just sequences of declarations. There are eight kinds of declaration (@figure-declaration-subtype-table), all of which begin with a unique keyword sequence. These sequences serve to delimit the declarations in a source file, and therefore make parsing simpler than in languages where top-level language elements are not explicitly distinguished from all other elements by keyword sequences (e.g. @python).

#let __syn_declaration_kind_table = table(
  columns: (auto, auto, 1fr),
  [*Name*], [*Keyword(s)*], [*Notes*],
  [_Module_], [`mod`], [Introduces a symbol for a submodule.],
  [_Import_], [`use`], [Introduces a symbol for a nonlocal item.],
  [_Type_], [`type`], [Defines a type and its constructors.],
  [_Type Alias_], [`type alias`], [Defines a non-recursive type alias.],
  [_External Type_], [`extern type`], [Introduces a symbol for a foreign type.],
  [_Function_], [`fn`], [Defines a function with its body.],
  [_External Function_],
  [`extern fn`],
  [Introduces a symbol for a foreign function.],

  [_Constant_], [`const`], [Defines a constant value.],
)

#figure(
  caption: [The declaration kinds.],
  __syn_declaration_kind_table,
) <figure-declaration-subtype-table>

The assignment of keywords to these declarations is drawn mostly from @rust, though the semantics of the type and external type declarations are substantially different; the type alias declaration does not draw its keywords from any extant language in particular.

#let __syn_type_decl_ebnf_grammar = {
  ```ebnf
  type declaration = ["|"], type constructor, { "|", type constructor } ;
  type constructor = ident, [ type constructor payload ] ;
  type constructor payload = record payload | tuple payload ;

  record payload = "{", [ record field { ",", record field }, [","] ], "}" ;
  tuple  payload = "(",   type expr,   { ",", type expr    }, [","],   ")" ;
  ```
}

#figure(
  caption: [A reduced EBNF grammar for type declarations],
  __syn_type_decl_ebnf_grammar,
) <figure-type-decl-ebnf-grammar>

Type declarations differ substantially from @rust in the form of their bodies, which are nonempty
#footnote[Because type declarations must have at least one type constructor, the user cannot define uninhabited types without using `!` (the canonical uninhabited type). Ocaml works around this with a language extension that makes the syntax ```ocaml type never = |``` a valid type declaration, since it doesn't have a primitive uninhabited type.]
lists of type constructors delimited by vertical bars (@figure-type-decl-ebnf-grammar). This syntax draws from @ocaml in particular, but can be found in most functional languages that descend from @ml.

=== Expressions <subsection-design-syntax-expressions>

Expressions are the largest of the major grammar subdivisions, and may only appear within constant and (non-external) function declarations. Much of the expression syntax is standard for a @c\-style language, though the lambda expression and block grammars are derived from @julia and @rust respectively.

#let __syn_expr_kind_table = table(
  columns: (auto, auto, 1fr),
  [*Name*], [*Example*], [*Notes*],
  [Identifier], [`foo`], [Refers to an item in the current scope.],
  [Path], [`foo.bar`], [Refers to an item by its module scope.],
  [Literal],
  [`3`, `true`, `"str"`, `'c'`],
  [Defines a value of a primitive type.],

  [List], [`['a', 'b']`], [Defines a list of values.],
  [Tuple], [`(x, y, z)`], [Defines a tuple of values.],
  [Record],
  [`T.RC { field: () }`],
  [Defines a value with a record constructor.],

  [Field], [`record.field`], [Refers to a field in a record or tuple.],
  [Lambda], [`() -> "return"`], [Defines an anonymous function.],
  [Call],
  [`f()`, `T.TC(0)`],
  [Calls a function or applies a tuple constructor.],

  [Prefix], [`!false`, `*ref`], [Invokes a prefix operator.],
  [Binary], [`x + y * z`], [Invokes a binary operator],
  [Match], [`match foo {..}`], [Performs structural pattern matching.],
  [If],
  [`if cond {..} else {..}`],
  [Executes some subexpression(s) conditionally.],

  [Paren], [`(..)`], [Explicitly defines precedence.],
  [Block],
  [`{ let x = 0; f(); x }`],
  [Defines a sequence of scoped subexpressions.],
)

#figure(
  caption: [The expression kinds.],
  __syn_expr_kind_table,
) <figure-expr-subtype-table>

Lambda expressions vary substantially in syntax among otherwise similar languages, and so the fact that they diverge here is unsurprising. The main source for Jabber's lambda expression syntax is @julia, but some details relating to their interactions with tuple patterns are instead drawn from @scala.

Because the `->` token is also used for function types and in the return types of function declarations, lambda expressions are a significant source of grammar complexity; parsing them naively requires potentially infinite lookahead!

=== Patterns <subsection-design-syntax-patterns>

Patterns are the most blatantly functional elements in Jabber's syntax because they are the syntactic surface for _structural pattern matching_, a feature that largely traces back to @ml and its descendants. They can appear in function parameters; in lambda expression parameters; in match arms; in let statements; in general they may appear wherever a name can be bound.

Most of the patterns in Jabber (@figure-pattern-subtype-table) derive from similar grammar rules in @rust and @gleam, though the _cons_ and _constructor_ patterns in particular are more closely related to the patterns in @ocaml and @idris2.

#let __syn_pat_kind_table = table(
  columns: (auto, auto, 1fr),
  [*Name*], [*Example*], [*Notes*],
  [Identifier], [`foo`], [Matches and binds any value of any type.],
  [Path],
  [`foo.bar`],
  [Matches a specific value with a constant or unit type constructor.],

  [Literal],
  [`()`, `true`, `"str"`],
  [Matches a specific literal value of a primitive type.],

  [Wildcard], [`_`], [Matches any value of any type.],
  [Tuple], [`(x, _, z)`], [Matches a tuple with a fixed length.],
  [List], [`[]`, `[x, y]`], [Matches a list with a fixed length.],
  [Cons], [`head :: tail`], [Matches a non-empty list of any length.],
  [Constructor],
  [`Ref { foo: _ }`],
  [Matches a value of a named type with a non-unit constructor.],

  [Paren], [`(_)`, `(_ :: tail)`], [Matches a value with the enclosed pattern.],
)

#figure(
  caption: [The pattern kinds.],
  __syn_pat_kind_table,
) <figure-pattern-subtype-table>

=== Types <subsection-design-syntax-types>

Types are the simplest of the major grammar subdivisions, and form a small sublanguage within the wider grammar; they may appear as part of declarations or as annotations for name bindings alongside patterns. Much of the syntax draws from @ml descendants like @ocaml and @haskell, and so this is the portion of the grammar that deviates the most from the norms of @gleam and @rust.

#let __syn_type_kind_table = table(
  columns: (auto, auto, 1fr),
  [*Name*], [*Example*], [*Notes*],
  [Identifier], [`Foo`], [A named type or a type variable.],
  [Path], [`foo.Foo`], [A type declaration, external type, or type alias.],
  [Infer], [`_`], [A placeholder for type inference.],
  [Primitive], [`int`, `()`], [A primitive type.],
  [Named], [`Foo[T]`], [A named type with generic arguments supplied.],
  [Function],
  [`(A, B) -> C`],
  [A function type with fixed domain and codomain.],

  [Paren], [`(A -> B)`], [A parenthesised type equivalent to its inner type.],
)

#figure(
  caption: [The type kinds.],
  __syn_type_kind_table,
) <figure-type-subtype-table>

_Function_ types are notable for drawing their syntax (@figure-function-type-ebnf-grammar) from @scala and @swift, since both languages arrived at similar solutions for denoting the types of higher-arity functions.

#let __syn_function_type_ebnf_grammar = {
  ```ebnf
  function type = (product domain | type), '->', type ;
  product domain = '(', type, {',', type,}, [','], ')', ;
  ```
}

#figure(
  caption: [A reduced EBNF grammar for function types.],
  __syn_function_type_ebnf_grammar,
) <figure-function-type-ebnf-grammar>

This solution to the problem of higher-arity functions is neat, but inherently makes typing a function of multiple arguments simpler than typing a function of one tuple argument.

== Packages and Source Files <section-design-packages-and-source-files>

Programs do not exist in a vacuum: at some point they must interact with the real world, and with one another! In Jabber, programs consist of _packages_, which in turn consist of _source files_. Package names must be globally unique, and the `core` package name is reserved for Jabber's core library.



#let __pkgs_example_file_tree = diagram(
  debug: 0,
  spacing: (4pt, 5pt),
  node((0, 0), `.`),
  edge((0, 0), (0, 1), (1, 1)),
  edge((0, 0), (0, 2), (1, 2)),
  node((1, 1), `jabber.toml`),
  node((1, 2), `src/`),
  edge((1, 2), (1, 3), (2, 3)),
  edge((1, 2), (1, 4), (2, 4)),
  edge((1, 2), (1, 5), (2, 5)),
  node((2, 3), `lib.jbr`),
  node((2, 4), `foo.jbr`),
  node((2, 5), `bar.jbr`),
)

#grid(
  columns: (1fr, 0.8fr),
  column-gutter: 8pt,
  [
    Physically, a package is a directory that contains a `jabber.toml` file and a `src` subdirectory for `.jbr` files. Submodules are then just nested subdirectories of `src` with names matching sibling `.jbr` files in the enclosing directory.

    A package must contain at least a root file at either `src/bin.jbr` or `src/lib.jbr`, with the names determining whether a package is a binary or library package respectively.
  ],
  grid.vline(stroke: gray),
  [
    #figure(
      caption: [An example package directory tree.],
      __pkgs_example_file_tree,
    ) <figure-package-file-tree-diagram>
  ]
)

The distinction between binary and library packages is as follows:

- A _binary_ package has a function in its root module called `main`, which becomes the entry-point to the resulting program when the package is compiled. Binary packages cannot be dependencies for other packages, i.e. they are always root packages in dependency #short("dag")s.
- A _library_ package has no particular requirements, and may be a dependency for other packages. They may be checked and compiled individually, but the resulting artifacts cannot be executed.

The `jabber.toml` file is simply a #short("toml") file that defines package metadata, principally its name and direct dependencies. Usage of #short("toml") as a configuration format for programming languages is well-attested, with both @rust @the-cargo-book[§3.1] and @julia @julia-the-pkg-manual[§10] using it as their primary configuration mechanisms.

== Semantics <section-design-semantics>

What follows in this section is an _informal_ description of Jabber's semantics as it relates to the design of the language. It focuses on key features of the semantic model that a programmer might be expected to know, and the elements of that model that differ significantly from other languages.

=== Programs and Runtime <subsection-design-semantics-runtime>

A _program_ is an executable artifact that, upon execution, will invoke a designated `main` function. The duration of this execution, which can potentially be interrupted or stopped entirely by external actors, is called the _runtime_ of the program. All properties of the semantic model are expected to hold during the runtime of a program and are entirely undefined otherwise.

Runtime is contrasted with _compile-time_, the period of time before the execution of the program where the Jabber compiler has access to the entire source code of the program and can act "in preparation" for the execution of the program.

=== Objects <subsection-design-semantics-objects>

An _object_ consists of the following elements:

+ A _type_.
+ 0 or more _invariants_.
+ 0 or more _members_.
+ An optional _destructor_.

The _lifetime_ of an object begins when it is constructed, and ends when it is no longer accessible to the remainder of the program.

The type of an object is inaccessible at runtime and cannot change for the entire lifetime of the object. In practice this means that the compiler is free to erase type information as much as possible, since it must be statically known at compile-time.

The invariants of an object are boolean-valued properties, defined either by the compiler or by social contract among programmers. These properties *must* remain true for the entire lifetime of the object. This is a significant difference from the norms of object-oriented languages like @cpp and @java, where there is an object construction period in which it is possible to access an object before its invariants have been established but _after_ its lifetime has begun.
#footnote[This is subject to interpretation of the relevant standards for the respective languages. By some readings, @cpp says that an object's lifetime only begins *after* its constructor returns to the caller.]

The members of an object are its runtime-accessible elements, and it *must* be possible to retrieve them in asymptotic-constant time. This retrieval is not necessarily direct, and members should be transformed and presented to the user in an appropriate form with respect to the type of the object where applicable.

The destructor of an object is a function that takes an argument of the type of the object and returns `()`. An object's destructor *may* be executed at some point between when it becomes inaccessible and when the program ends, and it *must* receive the object itself as an argument. No guarantee is made about the ordering of destructor invocations among distinct objects, and a program may end with outstanding destructor invocations that have not been executed.

=== Evaluation <subsection-design-semantics-evaluation>

Jabber uses a _strict_ evaluation model: expressions are evaluated based on their relative positions in the source code and in a deterministic order. This is in contrast to the lazy evaluation of languages like @haskell, where expressions are evaluated only as necessary.

In an expression, evaluation proceeds as follows:

- Blocks are evaluated statement-by-statement.
- In match and if-else expressions, the subject (either the scrutinee or the condition) is evaluated first, and then one of the outcomes (a match arm or branch) is evaluated afterwards.
- The body of a lambda expression is not evaluated, and will only execute if the value of the lambda expression is later used as the callee in a call expression.
- The arguments of a call expression are evaluated from left-to-right, and then the entire expression is evaluated with the results of the subexpressions as arguments.
- Prefix and binary operator expressions are treated as unary and binary call expressions with one or two arguments respectively, and are evaluated accordingly. The operands of a binary operator expression are evaluated from left-to-right.
- List, tuple, and record expressions evaluate their subexpressions from left-to-right.
- Parenthesised expressions are evaluated by evaluating their inner expressions.
- Field expressions first evaluate the _subject_ on the left side of the `.` before extracting a field from it.
- Literal expressions are not evaluated _per se_, but are instead replaced with their runtime values during compilation. They do not have side effects and so this is should be invisible to the user.

// TODO: write specific constraints for which expressions are allowed in constant declarations, and explain why they're necessary. we haven't defined a formal notion of "panicking," so explain in terms of potential side effects and non-termination.

=== Magic Functions <subsection-design-semantics-magic-functions>

// in which we discuss the magic functions, and their design implications

A _magic function_ is a polymorphic function that can specialise on particular types, and therefore cannot be written in ordinary Jabber code. These functions are necessary for polymorphic code, but must be defined for all possible types.

Jabber provides the `core.cmp.eq` and `core.cmp.neq`—both having the type signature `(T, T) -> bool`—as the functions corresponding to the `==` and `!=` operators respectively; this allows polymorphic code to check the equality of values whose type is unknown.

Two values of the same type `T` are equal if:
- `T` is a primitive type other than `!` and the values are identical.
- `T` is a tuple type and the values are pairwise-equal.
- `T` is a named type, the values belong to the same constructor in `T`, and the members of the each value are pairwise-equal.

The most notable part of this definition is that functions can never be equal to one another, even if the compiler knows they are equal. This is because function equality is undecidable in general, and the only other reasonable definition would be to use referential equality—that is, two functions are equal if they reference the same function object. Although some languages—for example @gleam—do use this strategy, they compromise by permitting that equality is not purely structural, thereby leaking some underlying implementation and runtime details. Many other languages have tried many other strategies to deal with this edge case, for example:

- @ocaml throws an exception @the-ocaml-system.
- @elm crashes @elm-core-basics.
- @sml has a notion of _eqtypes_ @the-definition-of-standard-ml[§4.4], effectively dividing its type system into types which can and cannot be compared. #footnote[In some sense this is _almost_ a kind of typeclass constraint, and in fact @elm extends this idea further into what it calls _constrained type variables_ @the-elm-guide.]

But since Jabber does not have exceptions, and crashing seems an overreaction, the simplest solution which preserves structural equality is to hold all functions mutually unequal.

== Type System <section-design-type-system>

Jabber's type system is most directly comparable with those of @gleam, @elm, and @ocaml,
#footnote[Ignoring the object-oriented elements of @ocaml's type system @the-ocaml-system[§3].]
which all use variations of @system-f. Type systems of this kind are effectively weakened forms of the untyped lambda calculus: they do not permit recursion and hence are not Turing-complete.

An important property of Jabber's type system is that it lacks the notion of a _type class_ and so cannot express type class constraints as in a language like @haskell or @rust. Though it is appealing, the implementation complexity of such a feature is substantial, and languages like @gleam explicitly eschew this kind of ad-hoc polymorphism in favour of faster compilation and conceptually simpler programs. As a consequence, all languages that make this choice must define some _magic functions_ (see @subsection-design-semantics-magic-functions) to serve as the atoms of polymorphic code @tapl[§23.2].

=== Primitive Types <subsection-design-type-system-primitive-types>

#let __prim_tys_table = table(
  columns: (auto, auto, 1fr),
  [*Name*], [*Keyword*], [*Meaning*],
  [Never],
  [`!`],
  [The canonical uninhabited type with no values, the $bot$ type.],

  [Unit], [`()`], [The canonical singleton type with a single value `()`.],
  [Boolean], [`bool`], [The canonical 2-type with values `true` and `false`.],
  [Character], [`char`], [The type of @unicode-scalar-value:pl.],
  [String],
  [`string`],
  [The type of well-formed @unicode-code-point sequences.],

  [Integer], [`int`], [The type of signed unbounded integers.],
  [Float],
  [`float`],
  [The type of IEEE-754 `binary64` @ieee-754-2019 floating point numbers.],
)

#figure(
  caption: [Jabber's primitive types.],
  __prim_tys_table,
) <figure-primitive-type-table>

Jabber's primitive types (@figure-primitive-type-table) are largely unremarkable, and have been designed to conform to the expectations of a user who is already familiar with the primitive types in other similar languages. Nevertheless, there are some details worth examining:

+ The _never_ type (`!`) is not present in any of @gleam, @elm, and @ocaml, and has been included for completeness with the rest of the type system. The `!` syntax for this type is derived from @rust.
+ The _unit_ type (`()`) is syntactically interesting because it conflates the type itself with its singleton value, so we may write `()` to mean both. This syntax is well-established by @elm, @gleam, and @rust, but prominent functional languages like @ocaml and @scala instead use separate keywords for their unit values and types.
+ The _integer_ type (`int`) is unbounded, making it closer to the integer types provided by @idris2 and @haskell than to the primitive integral types in @gleam and @ocaml. This unboundedness helps to avoid some of the awkward questions around the precise semantics of integer over-and-underflow.

=== Tuple Types <subsection-design-type-system-tuple-types>
In Jabber, a tuple type is a _fixed-length sequence of at least two types_, delimited by parentheses and interspersed by commas; they represent finite _products_ of types. For arbitrary types `A` and `B`, the following are tuple types:

- `(A, B)`
- `(B, B)`
- `(B, A, A, B)`

Tuples are then fixed-length heterogeneous sequences of values, where each value has the type corresponding to its index in the tuple type. The values in a tuple are called its _members_, and a valid tuple assigns to each of its members a value of the appropriate type.

Notice that this definition does not include the unit type
#footnote[Some languages treat the unit type as the 0-tuple, but in Jabber tuples must have at least two members. Still, it's worth pointing out that the `()` notation is usually meant to denote the 0-tuple!]
and strictly disallows tuples with only a single member. Although 1-tuple types are quite common—@julia, @rust, @gleam, and @scala all have them—they are largely pointless, since they are trivially isomorphic to their single member type. @idris2, @haskell, and @ocaml all disallow 1-tuples, and @idris2 even goes so far as to treat all tuples as right-associative pairs.

=== Function Types <subsection-design-type-system-function-types>
While most functional languages only deal with unary functions, Jabber permits functions with arbitrary arity and must therefore deal with a larger variety of function types; it is well known that functions of this kind are equivalent to the curried unary functions common among languages in the @ml tradition @tapl[§5.2].

A function type consists of a _domain_ and a _codomain_: the domain is a finite non-empty sequence of types that corresponds to the arguments a function of the type takes, while the codomain is simply the return type of a function of the type. A function which takes no arguments is treated as a function taking a single unit argument, thereby avoiding the need for a rigorous definition of a _nullary_ function.

The values of a function type are functions whose domains and codomains are identical to the domain and codomain of the function type.

=== Named Types <subsection-design-type-system-named-types>
Named types are the mechanism through which users are able to extend the type system with new types, and are introduced by type declarations; they consist of a _name_, some optional _generic parameters_, and at least one _constructor_. If a named type has no generic parameters then it is called _concrete_, whereas a named type with at least one generic parameter is called a _generic type_.

The constructors in a type declaration become the constructors of the named type, and come in three forms:

+ _Unit_ constructors take no arguments.
+ _Tuple_ constructors take one #footnote[
  Pedantically, this means that a tuple constructor can take only a single argument whereas an actual tuple must consist of at least two members; however this naming convention is well-established in Rust.
] or more arguments.
+ _Record_ constructors take a set of record fields as their argument.

#shortcolumns(
  [
    Constructors are accessed as though they were elements of a module whose name is their type, so in @figure-example-type-constructors-snippet `Named.Record` would refer to the constructor of `Named` whose name is `Record`.

  ],
  [
    #figure(
      caption: [Some example constructors.],
      ```jabber
      type Named =
        | Unit
        | Tuple(char, int)
        | Record { foo : string,
                   bar : string, }
      ```,
    ) <figure-example-type-constructors-snippet>
  ],
)

A named type can be marked with the `opaque` keyword, in which case its constructors are only visible in the module in which the type is defined. This feature allows for types that provide strong guarantees (e.g. a `Nat` type that wraps a nonnegative `int`) by preventing external consumers of an #short("api") from gaining access to its internals.

#shortcolumns(
  [
    There is a special case for types with a single constructor whose name exactly matches the name of the singular constructor; such types are called *structs* and their names can refer to both their constructors and the types themselves.

    For example, in @figure-example-struct-types-snippet the identifier `Ref` could be used both in the type `Ref[int]` and the pattern `Ref { contents }`.
  ],
  [
    #figure(
      caption: [Some example struct types.],
      ```jabber
      // a unit struct
      type Zero = Zero

      // a tuple struct
      type Triple[T] =
        Triple(T, T, T)

      // a record struct
      type Ref[T] =
        Ref { mutable contents: T }
      ```,
    ) <figure-example-struct-types-snippet>
  ],
)

=== Polymorphic Types <subsection-design-type-system-polymorphic-types>

Any identifier in a type which does not bind to a named type is a _type variable_, and any type containing type variables is said to be _polymorphic;_ types which are not polymorphic are called _concrete_. This follows in the @ml tradition, where polymorphic types are called _type schemes_ or _polytypes_ and concrete types are called _monotypes_ @tapl[§23.8].

Every type variable in a type is _quantified_ at the same _rank_, and so Jabber's type system is said to be _predicative_. This is in contrast to languages like @idris2 and @haskell, where in general types cannot be written in a _prenex_ normal form and so the `forall` keyword is necessary @tapl[§23.10].

It's important to explicitly state that type variables are *always* universally quantified in this context; the type system is not equipped to treat existential type variables as proper types. Existential type variables do still appear in Jabber, but this is only as a formal underpinning for type inference @tapl[§22.2].

=== Type Aliases <subsection-design-type-system-type-aliases>
Type aliases are _non-recursive type abstractions;_ that is, they are effectively functions of types that must necessarily terminate. While there are less aggressive ways to guarantee termination, type aliases largely exist to allow users to define shorthand synonyms for complicated types and so do not need quite so much computational power.

#shortcolumns(
  [
    In languages with very complicated type systems, type aliases are often seen as both highly necessary _and_ potential sources of confusion for users. @rust in particular is infamous for generating huge types in error messages that are otherwise hidden from the user with type aliases.
  ],
  [
    #figure(
      caption: [Example type aliases.],
      ```jabber
      type alias Always[T] =
        core.result.Result[T, !]

      type alias AlwaysErr[E] =
        core.result.Result[!, E]

      type alias Endo[T] = T -> T
      ```,
    ) <figure-example-type-aliases-snippet>
  ],
)

But it remains the case that a language with a highly complicated type system would be unwieldy without type aliases, potentially to the point of being unusable; they are a necessary evil of this kind of language design.

=== External Types <subsection-design-type-system-external-types>

When writing the signature for an external function, it will often be necessary to reason about types outside of the available Jabber source code. The solution to this problem comes in the form of user-defined external types, which serve as proxies for foreign types in the type system.

External types behave like opaque named types, and can only be created and consumed by external functions. They must be marked with annotations to define the external symbols they link to, as well as the #short("abi") they expect.

=== Uninhabited Types and Constructors <subsection-design-type-system-uninhabited-types>
A type `T` is _uninhabited_ if any of the following properties hold:

+ `T` is `!`.
+ `T` is a tuple with at least one uninhabited member.
+ `T` is a named type consisting of only tuple and record constructors, where:
  - each tuple constructor has at least one uninhabited argument, and;
  - each record constructor has at least one field whose type is uninhabited.

When a type contains both inhabited and uninhabited constructors, the compiler is free to discard the uninhabited constructors; this is a potential avenue for optimising the runtime representation of generic types. For example, the type `core.option.Option[T]` has two constructors: `Some(T)` and `None`. The type `Option[!]` would then be a singleton and could be entirely optimised away at runtime, since singleton types are zero-sized in the sense that they can be "stored" in 0 bits of information. #footnote[See @section-types-uninhabited-types and @section-types-singleton-types for the formal treatment of these notions.]

= A Model for Jabber Types <chapter-formal-types>

#quote(attribution: [_Jabberwocky_ by Lewis Carroll, 1871])[
  He took his vorpal sword in hand:\
  Long time the manxome foe he sought—\
  So rested he by the Tumtum tree,\
  And stood awhile in thought.
]

A great irony of functional programming languages in that they are quite poorly named: it is their _type systems_, rather than their functions, which most essentially characterise them. Languages like @idris2 and @haskell—which are otherwise so similar—are distinguished most effectively by the behaviour of their types.

But the term _type_ can refer to a huge range of things; to type declarations; to syntactic type expressions; to runtime representations of values; to abstract values of a certain sublanguage. From the perspective of @chapter-design, types are a syntactic object; in @chapter-impl they are an implementation detail. In this chapter we will analyse types as algebraic objects, having a certain underlying structure that essentially characterises them.

== Types In Jabber <section-types-types-in-jabber>

We draw a tripartite distinction between _types,_ _type expressions,_ and _type declarations._

Every expression in a Jabber program has a canonical
#footnote[
  Unique up to change of variables.
]
type that dictates which functions it may be passed to as an argument; for this purpose types can be seen as abstract symbols connoting properties of expressions. The purpose of this chapter is to formalise the semantics of types in Jabber with a mathematical model, from which properties of the type system can be derived.

A type _expression_ is then a literal (possibly incomplete) representation of a type within the source of a Jabber program. We have already seen the form of type expressions in the grammar (@subsection-design-syntax-types), but not every syntactically well-formed type expression is a semantically coherent type. In particular, it may happen that
+ a name can fail to resolve to a type declaration or type variable, or;
+ a name can resolve to a declaration which cannot be treated as a type, or;
+ type inference can fail to find an unambiguous assignment for an inference placeholder.

We will presume in the remainder of this chapter that these errors cannot occur, and hence that all names in type expressions are appropriately bound and all instances of the inference placeholder have been replaced.

A type _declaration_ is either a (nominal) type, external type, or type alias declaration (see @subsection-design-syntax-declarations). Each of these declarations introduces a new symbol that can be used in a named type expression, as well as some additional information specific to each kind of declaration. For the remainder of this chapter, we will consider external type declarations to be equivalent to type declarations with the `opaque` modifier.

== Algebraic Structure

There are a number of statements about Jabber's type system that are intuitively true, like
+ `bool` and `Option[()]` are essentially the same type.
+ `Result[T, !]` is essentially the same as `T` for any type `T`.
+ `((), T)` is essentially the same as `T` for any type `T`.
+ `(!, T)` is essentially the same as `!` for any type `T`.
+ `Result[T, E]` and `Result[E, T]` are essentially the same for any types `T` and `E`.

Statements like these are claims about the inherent _structure_ of types, where we hold that two types can be equivalent even if they have different names. They are also _algebraic_ claims, and we will see that these examples are equivalent to the following propositions:

+ $2 = 1 + 1$.
+ $T + 0 = T$.
+ $1 times T = T$.
+ $0 times T = 0$.
+ $T + E = E + T$.

We will see that in the taxonomy of abstract algebra, Jabber's type system is best analysed as a commutative unital semiring.
#footnote[Equivalently it is the combination of two commutative monoids, each corresponding to the $+$ and $times$ operators.] This will enable us to prove several results about the structure of the type system, including a number that are used by compiler optimisations in @chapter-impl.

The algebraic perspective is not the only way to analyse the structure of a type system—indeed, techniques from category theory are generally more common @crole-categories-as-types @algebraic-models-of-simple-type-theories. Still, the techniques and notions of abstract algebra are more well-known than those of category theory, and as a result this analysis is generally more accessible.

== Representing Types <section-types-representing-types>

It is well-known that $n$-ary functions as in Jabber can be equivalently written in the _curried_ unary style @tapl[§5.2], where in particular nullary functions become unary functions with the unit domain. Usefully, this representation flattens the distinction between nullary and unary function types like `() -> T` and `((),) -> T`; this reflects the fact that such types are fundamentally equivalent.


Similarly, tuple and record types are known to be fundamentally equivalent and representable as nested _pairs_ @tapl[§11.6]; such types are uniquely defined by their projections and called _product_ types in reference to the category-theoretic and Cartesian products @maclane-categories[§II.3]. Dually we also have _coproduct_ types given uniquely by their constructors @maclane-categories[§III.3], which can be defined in Jabber using type declarations. As with product types, coproducts can be defined inductively by nesting binary _sums_ @tapl[§11.9].

In all three cases, we can render types faithfully while ignoring some of their surface details. But notice the problem this introduces; what does it mean for two types to be equal? If we take $+$ to be the coproduct, then `bool` and `Option[()]` would both become $() + ()$, even though they are clearly distinct types. We will address this problem when we discuss isomorphisms of types.


== Formal Types <section-types-formal-types>

We begin by defining a language of types, starting with its simplest elements.

#definition[
  $"Symbol" = {bold(a), ..., bold(z), bold(A), ..., bold(Z)}^+$ is an infinite set of alphabetic symbols.
]

#remark[
  Symbols will be written in *bold* to distinguish them, for example $bold(x)$, $bold("y")$, and $bold("float")$.
]

Many components of Jabber's type system will be identified as symbols, including almost every identifier. The set of symbols will function as a black box from which to generate names.

#let __tys_formal_type_bnf_grammar = {
  $
    "Type" tau, upsilon &::= \
    &space| bold(x) &"(symbol)" \
    &space| 0 &"(bottom)" \
    &space| 1 &"(unit)" \
    &space| tau + upsilon &"(coproduct)" \
    &space| tau times upsilon &"(product)" \
    &space| tau -> upsilon &"(function)" \
    //&space| tau space upsilon quad &"(application)" \
    //&space| forall t. space tau quad &"(universal)" \
  $
}

#definition[
  The language $"Type" subset ("Symbol" union {0, 1, +, times, ->, forall, .})^+$ is defined as

  #align(center, __tys_formal_type_bnf_grammar)
] <definition-formal-type-set>

@definition-formal-type-set provides a language of types, but not a semantics with which to understand it. We need to identify its relationship with Jabber's surface syntax, and then we may discuss its meaning. First, we need to give a more precise description of that surface syntax, in terms of type expressions and type declarations.

#definition[
  The language $"TyExpr" subset "Jabber"$ is defined as
  $
    "TyExpr" a, b, c &::= \
    &space| bold(x) &"(symbol)" \
    &space| ! &"(never)" \
    &space| () &"(unit)" \
    &space| bold("bool") &"(boolean)" \
    &space| (a, ..., b) &"(tuple)" \
    &space| (a, ..., b) -> c &"(function)" \
    &space| bold(x)[b, ..., c] &"(named)" \
  $
] <definition-type-expr-set>

#remark[
  Notice that @definition-type-expr-set explicitly distinguishes `bool` as a type expression, but leaves the other primitive types implicit as symbols. This is because the cardinality of `char`, `int`, `float`, and `string` is not fixed, and can vary across architectures; we therefore leave them as opaque symbols for the purpose of this analysis.
]

To define type declarations, we also need to describe their constructors.

#definition[
  The language $"TyConstr" subset "Jabber"$ is defined as
  $
    "TyConstr" &::= \
    &space| bold(x) &"(unit)" \
    &space| bold(x)(a, ..., b) &"(tuple)" \
    &space| bold(x){ bold(y) : a, ..., bold(z) : b } &"(record)" \
  $
]

#definition[
  $"TyDecl"$ is the subset of $"Symbol" times cal(P)("TyConstr")$ where the right side of each pair is a finite set.
]

Thus we can model a type declaration as just a pair, where the left component is its name and the right component is the set of its constructors. We can use this model to express external and opaque types as well, by simply giving them as $(bold(x), {bold(x)})$—that is, opaque types are those with a single unit constructor matching their name exactly.

#definition[
  The function $"constrs" : "TyExpr" -> { "TyConstr" }$ sends a type to the set of its constructors if it is named, and the empty set otherwise.
]

#remark[
  This function is effectively a magic way to produce the constructors of a type without worrying about type variables and type application.
]

We now have the necessary elements in place to describe the relationship between these surface syntax definitions and the formal types in @definition-formal-type-set; we begin with type expressions.

#definition[
  The functions $bracket.l.double dot.c bracket.r.double_"TyExpr" : "TyExpr" -> "Type"$ and $bracket.l.double dot.c bracket.r.double_"TyConstr" : "TyConstr" -> "Type"$ are defined such that

  $
    bracket.l.double bold(x) bracket.r.double_"TyExpr" &= bold(x)\
    bracket.l.double ! bracket.r.double_"TyExpr" &= 0\
    bracket.l.double () bracket.r.double_"TyExpr" &= 1\
    bracket.l.double bold("bool") bracket.r.double_"TyExpr" &= 1 + 1\
    bracket.l.double (
      a, ..., b
    ) bracket.r.double_"TyExpr" &= bracket.l.double a bracket.r.double_"TyExpr" times dots.c times bracket.l.double b bracket.r.double_"TyExpr"\
    bracket.l.double () -> a bracket.r.double_"TyExpr" &= (

    ) -> bracket.l.double a bracket.r.double_"TyExpr"\
    bracket.l.double (
      a_1, ..., a_n
    ) -> b bracket.r.double_"TyExpr" &= bracket.l.double a_1 bracket.r.double_"TyExpr" -> dots.c -> bracket.l.double a_n bracket.r.double_"TyExpr" -> bracket.l.double a_b bracket.r.double_"TyExpr"\
    bracket.l.double bold(x)[a, ..., b] bracket.r.double_"TyExpr" &= sum_(c in "constrs"(bold(x)[a, ..., b])) bracket.l.double c bracket.r.double_"TyConstr"\
    #v(1em)\
    bracket.l.double bold(x) bracket.r.double_"TyConstr" &= 1 \
    bracket.l.double bold(x)(a, ..., b) bracket.r.double_"TyConstr" &= bracket.l.double a bracket.r.double_"TyExpr" times dots.c times bracket.l.double b bracket.r.double_"TyExpr" \
    bracket.l.double bold(x){bold(y) : a, ..., bold(z) : b} bracket.r.double_"TyConstr" &= bracket.l.double a bracket.r.double_"TyExpr" times dots.c times bracket.l.double b bracket.r.double_"TyExpr" \
  $ where $sum$ is shorthand for an iterated coproduct.
]

#remark[
  To a certain extent we've jumped the gun and assumed commutativity for $+$ and associativity for $times$, but these are fairly self-evident properties of the type system.
]

This is somewhat dense, so let's consider an example: recall the earlier claim that `bool` and `Option[()]` map to the same type in this representation.

#example[
  For `bool`, we have $bracket.l.double bold("bool") bracket.r.double_"TyExpr" = 1 + 1$ by definition. For `Option[()]`, the corresponding type expression is $bold("Option")[()]$, and $"constrs"(bold("Option")[()]) = {bold("Some")(()), bold("None")}$. From this we have
  $
    bracket.l.double bold("Option")[
      ()
    ] bracket.r.double_"TyExpr" &= bracket.l.double bold("Some")(
      ()
    ) bracket.r.double_"TyConstr" + bracket.l.double bold("None") bracket.r.double_"TyConstr" \
    &= bracket.l.double () bracket.r.double_"TyExpr" + 1 \
    &= 1 + 1
  $ as expected.
]

== Type Equivalence

Obviously, choosing to denote types with numbers is very suggestive; we would quite like to be able to write $1 + 1 = 2$, #footnote[This is why `bool` is called the canonical $2$-type!] or demonstrate that $0 times tau = 0$. But remember that these types are just words in a language! From the purely symbolic perspective, it is obvious that $1 + 1 != 2$. We therefore need to relax our constraints and define an _equivalence_ of types instead, drawing on the expected algebraic behaviour of $0$ and $1$.

#definition[
  Let $tau, upsilon in "Type"$; we say they are equivalent, and write $tau equiv upsilon$, whenever
  + $tau = upsilon$, or
  + $tau = tau_1 -> tau_2$, $upsilon = upsilon_1 -> upsilon_2$, and $tau_1 equiv tau_2 and upsilon_1 equiv upsilon_2$, or
  + $tau = upsilon + 0$ or $tau = 0 + upsilon$, or
  + $tau = upsilon times 1$ or $tau = 1 times upsilon$, or
  + $tau = tau_1 times (tau_2 + tau_3)$ and $upsilon = tau_1 times tau_2 + tau_1 times tau_3$, or
  + $tau = (tau_1 + tau_2) times tau_3$ and $upsilon = tau_1 times tau_3 + tau_2 times tau_3$.
]

#remark[
  Though slightly broader, this is the definition of a commutative unital semiring; because both addition and multiplication are commutative here we can omit the usual absorption axioms in favour of a simple proof.
]

As a small example of type equivalence, we can prove that $0$ is the absorbing element for $"Type"$.

#theorem[
  Let $tau in "Type"$; then $0 times tau equiv tau times 0 equiv 0$.
]

#proof[
  $0 times tau equiv (0 + 0) times tau equiv 0 times tau + 0 times tau$, hence $0 times tau equiv 0 times tau + 0 times tau$. This can only hold if $0 times tau equiv 0$; by similar argument we also have that $tau times 0 equiv 0$. #footnote[We rely here also on the fact that the zero element of any monoid is unique.]
]

#remark[
  Consider what this theorem means in the context of the full type system: any types of the forms `(!, T)` and `(T, !)` are equivalent to `!`. This tracks with our understanding of `!` as a type without values, since constructing an element of a product type requires values from each of the constituent types; hence you cannot form a value of type `(T, !)` because you would first require a value of type `!`, and so `(T, !)` obviously has no values.
]

== Uninhabited Types <section-types-uninhabited-types>

In the previous chapter, uninhabited types were described as "types with no values." We can now give a more precise definition as follows.

#definition[
  A type $tau in "Type"$ is _uninhabited_ if and only if $tau equiv 0$.
]

Obviously we have $0 equiv 0$, but now we have the tools to prove some slightly more interesting results about uninhabited types.

#theorem[Let $tau, upsilon in "Type"$ with $tau$ uninhabited; then $tau times upsilon$ is uninhabited.] <theorem-uninhabited-prod-is-uninhabited>

#proof[$tau times upsilon equiv 0 times upsilon equiv 0$.]

#theorem[Let $tau, upsilon in "Type"$ both uninhabited; then $tau + upsilon$ is uninhabited.] <theorem-uninhabited-coprod-uninhabited-is-uninhabited>

#proof[$tau + upsilon equiv 0 + upsilon equiv upsilon equiv 0$.]

We can also extend this definition back to the surface syntax in terms of type expressions, which makes rigorous the earlier definition of an uninhabited type expression.

#definition[
  A type expression $a in "TyExpr"$ is uninhabited if and only if $bracket.l.double a bracket.r.double_"TyExpr" equiv 0$.
]

== Singleton Types <section-types-singleton-types>

As with uninhabited types, our definition of singleton types can be made more precise in this system.

#definition[
  A type $tau in "Type"$ is a _singleton_ if and only if $tau equiv 1$.
]

Again, we obviously have $1 equiv 1$, but we can also prove some more interesting results.

#theorem[Let $tau, upsilon in "Type"$ both singletons; then $tau times upsilon$ is a singleton.] <theorem-singleton-prod-singleton-is-singleton>

#proof[$tau times upsilon equiv 1 times upsilon equiv upsilon equiv 1$.]

#remark[ Without making this observation rigorous, @theorem-singleton-prod-singleton-is-singleton is obviously the dual of @theorem-uninhabited-coprod-uninhabited-is-uninhabited. ]

To complete the analogy with uninhabited types, we can also extend the definition of a singleton type back to the surface syntax in terms of type expressions.

#definition[
  A type expression $a in "TyExpr"$ is a singleton if and only if $bracket.l.double a bracket.r.double_"TyExpr" equiv 1$.
]

== Isomorphisms of Types

In several places in this report, references are made to certain types being isomorphic. We may now define exactly what it means for two type expressions in Jabber's surface syntax to be isomorphic.

#definition[
  Let $a, b in "TyExpr"$. We say they are isomorphic, and write $a tilde.equiv b$, if and only if $ bracket.l.double a bracket.r.double_"TyExpr" equiv bracket.l.double b bracket.r.double_"TyExpr". $
]

#remark[
  In some sense this is almost a tautology; it is the statement that two type expressions are equivalent if their underlying algebraic structures are equivalent.
]

#example[
  The `Result` type found in most functional languages #footnote[In many languages it is also called `Either`.] is sometimes described as symmetric, which we can interpret as the statement $bold("Result")[bold(x), bold(y)] tilde.equiv bold("Result")[bold(y), bold(x)]$. We can show this as follows:
  $
    "constrs"(bold("Result")[bold("x"), bold("y")]) &= {bold("Ok")(bold(x)), bold("Err")(bold(y))} \
  #v(1em) \
  bracket.l.double bold("Result")[bold(x), bold(y)] bracket.r.double_"TyExpr" &= bracket.l.double bold("Ok")(bold(x)) bracket.r.double_"TyConstr" + bracket.l.double bold("Err")(bold(y)) bracket.r.double_"TyConstr" \
  &= bold(x) + bold(y) \
  &equiv bold(y) + bold(x) \
  #v(1em) \
  therefore bold("Result")[bold(x), bold(y)] &tilde.equiv bold("Result")[bold(y), bold(x)].
  $
]

= Implementation <chapter-impl>


#let __cd_group(row, color) = node(
  enclose: ((0, row), (2, row)),
  snap: false,
  inset: 10pt,
  stroke: stroke(
    paint: color,
    thickness: 1pt,
    dash: (6pt, 3pt),
    join: "bevel",
  ),
)

#let __cd_front_color = red.darken(10%)
#let __cd_middle_color = green.darken(30%)
#let __cd_back_color = blue

#let compiler_architecture_diagram = diagram(
  debug: 0,                 // debug level
  cell-size: (8em, 4em),   // row/column sizes
  node-stroke: 0.6pt,       // node border stroke weight
  node-shape: rect,         // node border shape
  node-outset: 4pt,         // node/edge gap size
  spacing: (3em, 2em),      // row/column gutter sizes
  node((0, 0), `Lexing`, height: 3em, width: 6em),
  edge("r", "->", `tokens`),
  node((1, 0), `Parsing`, height: 3em, width: 6em),
  edge("r", "->", `CST`),
  node((2, 0), `Abstraction`, height: 3em, width: 6em),
  //node((2.5, 0), `FRONT`, snap: false),
  edge("d", "->", `AST`, label-side: left),
  node((2, 1), `Name Resolution`, height: 3em, width: 6em),
  edge("l", "->", `AST`),
  node((1, 1), `Type Checking`, height: 3em, width: 6em),
  edge("l", "->", `AST`),
  node((0, 1), [`Static Analysis`], height: 3em, width: 6em),
  edge("d", "->", `AST`),
  node((0, 2), `Lowering`, height: 3em, width: 6em),
  edge("r", "->", `IR`),
  node((1, 2), `Code Generation`, height: 3em, width: 6em),
  edge("r", "->", `IR`),
  node((2, 2), `Rendering`, height: 3em, width: 6em),

  // node groups
  __cd_group(0, __cd_front_color),
  __cd_group(1, __cd_middle_color),
  __cd_group(2, __cd_back_color),
)

#figure(
  caption: [The standard compiler architecture.],
  compiler_architecture_diagram,
) <standard-compiler-architecture-diagram>

While compilers are often large and idiosyncratic projects, they have coalesced around a standard architecture with remarkably little deviation. By convention, we divide this common structure into three _stages_: the #text(fill: __cd_front_color)[front end], the #text(fill: __cd_middle_color)[middle end], #footnote[The term _middle end_ is a consequence of the pervasiveness of the terms _front end_ and _back end_, and in some contexts it is instead called the _optimiser_. ] and the #text(fill: __cd_back_color)[back end].

The front end of a compiler is responsible for interacting with raw source code and producing representations of the syntactic structure thereof; it is often also responsible for analysing and reporting syntax errors where possible. The key data structures in this stage are the _concrete syntax tree_ (#short("cst")) and the _abstract syntax tree_ (#short("ast")), which provide varying levels of syntactic detail. Tools like formatters and syntax highlighters are often implemented in this section, since they usually don't require static analysis to function correctly.

The middle end of a compiler is perhaps the most variable stage, as it is responsible for the bulk of the static analysis in the pipeline. Name resolution and type checking are among the most common tasks in this stage, but the language being compiled will usually dictate other necessary analysis steps; for example the @koka compiler performs effect checking in this stage, while the @rust compiler does borrow checking. The data structures in this stage are various kinds of AST and _intermediate representation_ (IR), as well as the miscellaneous data structures required to implement particular kinds of static analysis (e.g. @union-find data structures for type checking).

The back end of a compiler is distinguished from the other stages by being _architecture-dependent_, in that it requires special knowledge of the target. A target may be a literal machine, or a virtual machine, or even another programming language, but in all cases the back end must be able to preserve the semantics of a program during code generation. The output of this stage is highly dependent on the target in question, and will often not be directly executable; compiler backends like @llvm emit _object files_ which must first be _linked_ into an executable, though this process is usually managed by a separate driver program rather than the compiler itself.

== Compiler Architecture <section-impl-compiler-architecture>

The Jabber compiler is implemented in @rust, with the majority of its functionality provided by the `jabber` crate in `/compiler`. This crate is responsible for almost everything discussed in this chapter with the exception of the parser in `/tree-sitter-jabber` (discussed in @section-impl-parsing). Refer to @appendix-dependencies for the dependencies used by the primary crate.

== Package Loading <section-impl-package-loading>

Before any stage of the compiler pipeline can be run, it first needs some input. Obtaining and organising this input is the job of the _package loader_, which takes as input the description of a package (hereafter referred to as the _root_ package) and returns a collection of packages ordered such that no package appears before its dependencies.

#let example_package_graph_diagram = diagram(
  debug: 0,
  node-shape: circle,
  node-stroke: 0.6pt,
  node-outset: 2pt,
  node((0, 0), `root`),
  edge((0, 2.2), "->"),
  edge((-1, 1), "->"),
  edge((0.3, 1.3), "->"),
  edge((1, 1), "->"),
  node((-1, 1), `A`),
  edge((0, 2.2), "->"),
  node((1, 1), `B`),
  edge((0.3, 1.3), "->"),
  edge((0, 2.2), "->"),
  node((0.3, 1.3), `C`),
  edge("->"),
  node((0, 2.2), `core`),
)

#shortcolumns(
  [
    The transitive closure of a package with its dependencies forms a #short("dag") (@figure-package-graph-diagram), and so the package loader is always able to choose an ordering—namely a _topological_ ordering—such that every package is preceded by its dependencies.

    Notice also that every package other than `core` depends directly on `core`: it is the terminal element in every dependency graph and must therefore appear first in a well-ordered collection of packages.
  ],
  [
    #figure(
      caption: [A simple package graph.],
      example_package_graph_diagram,
    ) <figure-package-graph-diagram>
  ],
)

The other main task of the package loader is to load source files from disk into memory, and then to associate them with their packages. Though this is a relatively mundane task, it constitutes a significant portion of the total execution time of the pipeline.
#footnote[This is due to the relatively high cost of file system IO, which is likely to diminish over repeated compiler invocations as the host OS moves the contents of source files to in-memory caches.]

== Parsing <section-impl-parsing>

Both the lexing and parsing stages in the compiler are implemented with the Tree-sitter parser generator, which compiles a grammar written in a @javascript\-based #short("dsl") into a small bundle of @c artifacts; the compiler then loads these artifacts at runtime as a `cst::Parser` instance that can be used to parse source files. The result of parsing is a `cst::Cst` instance, a #short("cst") preserving as much information as possible about a source file.

Tree-sitter's CSTs are homogeneous rooted trees with each node having both a _kind_ ID and a location; nodes are located both in terms of byte offsets and row/column offsets. To reduce their memory footprint, these trees do not store textual data inline and further analysis of the source code requires access to the original source file's contents.

The grammar (defined in `tree-sitter-jabber/grammar.js`) is fundamentally a list of context-free grammar rules whose start symbol is `source_file`, and whose terminal symbols are string literals and regular expressions. This grammar is slightly more permissive than the grammar given in @appendix-formal-grammar, with the full validation of the source syntax being deferred until later in the pipeline to produce more informative error messages.

Internally, `jabber_core` relies on the `type-sitter` crate to interact with the Tree-sitter parser. This is because Tree-sitter generates a `node-types.json` file describing a static type schema for the parser, which `type-sitter` uses to generate typed bindings. Additionally, `type-sitter` generates typed bindings for Tree-sitter query files defined in a @scheme #short("dsl"), which are used for simple pattern-matching analysis of CSTs.

== Abstraction <section-impl-abstraction>

The later compiler stages do not require the full representation of syntactic information provided by a CST, and so we must first _abstract_ the information they contain; this process produces an AST. There are several different ASTs defined in `jabber_core::ast`, but this compiler stage is only concerned with those defined in the `unbound` and `unbound_lowered` submodules.

Before a `cst::Cst` instance is abstracted, it is first traversed to locate syntax errors. If any errors are found, they are returned to the caller and the abstraction is aborted. For the remainder of the stage, `cst::Cst` instances are guaranteed to contain no syntax errors, and no later compiler stage will have to concern itself with the potential presence of syntax errors. During abstraction, `cst::Cst` instances are traversed recursively and their nodes are converted into the appropriate corresponding types in `ast::unbound`. The final result is an `ast::unbound::Ast` instance.

Like `cst::Cst` instances, `unbound::Ast` instances do not store string data inline but instead contain `span::Span` values representing half-open byte intervals in the contents of a source file. Because the types in the AST are known statically at compile-time, and because a single `span::Span` value is several times smaller than the location information stored in a CST node,
#footnote[On 64 bit systems `type_sitter::raw::Range` has a size of 48 bytes, 6 times larger than `span::Span.`]
`unbound::Ast` instances consume much less memory than the `cst::Cst` instances from which they are created.

The final portion of this stage converts from `ast::unbound` to `ast::unbound_lowered`, but this is fundamentally interwoven with the construction of the `env::Env` in @section-impl-name-resolution and is more fully treated in that section instead.

== Name Resolution <section-impl-name-resolution>

The implementation of name resolution in `jabber_core` is broken into three distinct phases, governing the construction and processing of various _environments_ (@figure-name-resolution-phases-table). For all remaining compiler stages, the accumulated information about the source code will be stored in some kind of contextual environment.

#let __nr_arch_table = table(
  columns: (auto, auto, 1fr),
  [*Section*], [*Environment Type*], [*Notes*],
  [@subsection-impl-name-resolution-env-construction],
  [`unbound::UnboundEnv`],
  [Lowers all instances of `ast::unbound::Ast` to types in `ast::unbound_lowered`, and assigns stable IDs to all packages, modules, and items.],

  [@subsection-impl-name-resolution-import-res],
  [`import_res::ImportResEnv`],
  [Resolves import paths globally among `use` declarations, potentially generating an error if import cycles are detected. ],

  [@subsection-impl-name-resolution-local-name-res],
  [`resolve::ResEnv`],
  [Resolves all other names in all ASTs, producing an environment table which may still contain resolution errors.],
)

#figure(
  caption: [The distinct phases of name resolution in `jabber_core`.],
  __nr_arch_table,
) <figure-name-resolution-phases-table>

The design of the central `jabber_core::env::Env` data structure is heavily influenced by the similar `Env.env` type used in the @austral compiler @design-of-the-austral-compiler[§6.2], which models a simple in-memory relational database.

In the metaphor of a relational database, the fields of the environment are vectors representing _tables_, and the indices into those vectors are the corresponding _keys_.
#footnote[Indices are wrapped in newtypes like `TermId` so that they can only be used with the correct table.]
Because we require these indices to be stable, it is an invariant of the environment that elements cannot be deleted or reordered.

#let __nr_env_definition_code_snippet = {
  ```rust
  pub struct Env<Te, Ty, I> {
      files: Vec<SourceFile>,
      packages: HashMap<Symbol, Package>,
      modules: Vec<Module<I>>,
      terms: Vec<Term<Te>>,
      types: Vec<Type<Ty>>,
      interner: StringInterner,
  }
  ```
}

#grid(
  columns: (0.8fr, 1fr),
  column-gutter: 8pt,
  [
    The environment is the central data structure for the majority of the middle-end stages, and hence is parameterised over `Te` (_term_), `Ty` (_type_), and `I` (_identifier_); the types `UnboundEnv`, `ImportResEnv`, and `ResEnv` are just type aliases that assign differing types to these parameters.
  ], grid.vline(stroke: gray),
  grid.cell(
    align: horizon,
    figure(
      caption: [The definition of `env::Env`.],
      __nr_env_definition_code_snippet,
    ),
  ),
)

Of special note is the `interner` field, which points to a buffer of interned strings that can be indexed by `symbol::Symbol` values. String interning is particularly useful here, both because interned strings have an $O(1)$ comparison operation, and because the same string literal is likely to appear in many locations throughout a given body of source code.

=== Phase 1 – Environment Construction <subsection-impl-name-resolution-env-construction>

Prior to performing name resolution, the compiler must first load the disparate collection of packages and source files into the environment, effectively flattening their structure while retaining information about the relationships between them. By relying on the correctness of the topological ordering of the packages established by the package loader (@section-impl-package-loading), the environment can be constructed package-by-package without the risk of accidentally referring to an unseen package.

Each package is loaded as follows:

+ The package and its dependencies are passed to `UnboundEnv::consume_package`.
  - The `core` library is added to every package as an additional dependency.
  - Dependencies are passed by their `Symbol` names, to guarantee that they have already been loaded into the environment.
+ The root file of the package is loaded and registered as a module in the environment.
+ The package is registered and inserted into the environment.
+ The remaining source files are recursively loaded and registered. Source files are loaded eagerly, since it is possible that they are not actually accessible from the root module but this cannot be known until the later stages of name resolution.
+ The name of the package, along with any errors and warnings generated by loading the remaining source files, are returned to the caller.

The resulting `UnboundEnv` can then be used to build an `ImportResEnv` during the next phase of name resolution.

=== Phase 2 – Import Resolution <subsection-impl-name-resolution-import-res>


This name resolution phase is responsible for resolving imported names across packages and among all modules, and therefore also for reporting an error if an import cycle
#footnote[An _import cycle_ is a cycle in the graph of import declarations. Every import declaration in a cycle cannot be resolved to a concrete name, and name resolution cannot advance further in these cases.]
is present. The entrypoint is the `ImportResEnv::from_unbound_env` function, which consumes the `UnboundEnv` from the the previous phase and returns a newly constructed `ImportResEnv` along with a list of any errors that arose in the process.

Import resolution is implemented by the `ImportResEnv::resolve_imports` function, which takes a list of unresolved imports and proceeds in two stages:

+ Imports are _normalised_ to `NormalImport` values and checked for name collisions.
+ The normal imports are resolved to their concrete items.

This second stage is implemented as a _fixed-point_ algorithm, which loops repeatedly until there are either no more unresolved imports or all remaining imports are members of import cycles. A fixed-point algorithm is necessary in this case because unresolved imports may depend on other unresolved imports, and so iteratively resolving the entire collection of imports is the only way to guarantee it is adequately processed.
#footnote[This approach was inspired by a prototype name resolution algorithm for @rust published by Niko Matsakis in 2015 @rust-resolver-algorithm-github.]

=== Phase 3 – Local Name Resolution <subsection-impl-name-resolution-local-name-res>

The vast majority of name resolution happens in this final phase, where the #short("ast")s from `ast::unbound_lowered` are converted into their corresponding representations in `ast::bound`. The entrypoint here is the `env::resolve::resolve` function, which takes an `ImportResEnv` along with some error handling context and returns a `ResEnv`.

#short("ast")s are traversed and processed by a `Resolver` struct, which has visitor methods corresponding to all the possible forms of an `ast::unbound_lowered::Ast`. A `Resolver` also keeps track of a `Scope` stack, and scopes are pushed and popped as appropriate. Some special handling is provided for block expressions, since they can contain an unbounded number of scopes that need to be removed when the block's scope is removed.

There are several different kinds of names to consider during resolution:
- Ordinary names—like regular variables—just resolve to a name in scope.
- Binding names introduce a new name (probably in a new scope) and can shadow other names already in scope. Examples include the assignee in a `let` statement and lambda expression parameter patterns.
- Weak binding names are like ordinary names, except that if they fail to resolve they will instead introduce a new name as if they were a binding name. Function parameter types are the best example of this, and most (but not all) types act like this.

Declarations associated with types—_type_, _external type_, and _type alias_ declarations—are processed before all others, since information about them is necessary when resolving paths and type expressions in other kinds of declarations. The remaining unresolved declaration kinds are the _function_, _external function_, and _constant_ declarations, and are collectively called _terms_; they can contain expressions and so the bulk of the name resolution implementation exists to handle them.



=== Remarks
While implementing the name resolution portion of the compiler, I found it quite difficult to find extant literature—whether published formally or otherwise—that discussed the details of implementing name resolution. Many sources skimmed over this domain, and where they did provide more detail it was often only in regards to the algorithm itself. Indeed, the _only_ example I encountered that emphasised the data structures involved over the algorithm was in an article discussing the design of the @austral compiler @design-of-the-austral-compiler.

Name resolution is the start of the compiler's middle-end, and hence the stage at which the primary data structure must change from representing _trees_ to representing _graphs_. I would identify it as a key milestone in the implementation of the compiler, and worth discussing in its own right.

Separately, it's worth emphasising that in principle the compiler could disambiguate and resolve names in far more pathological cases than it does currently. The limiting factor here is not due to the implementation but in the design of Jabber itself; most contexts in which the compiler could use complicated name resolution schemes are already held to be illegal by the language.

== Type Checking <section-impl-type-checking>

The final stage of the middle end is _type checking;_ it is responsible for verifying that there are no type mismatches in the program, and that the entire program has a concrete type. It is arguably the most complex part of the middle end, and certainly consumed the most time overall during development.

We can divide type checking into two _phases_, though they are not of equal complexity. The first phase is the lesser of the two, responsible for a number of preprocessing tasks necessary in the second phase. It is implemented in `env::typed::lower`, whereas the larger second phase is in `env::typed`. The second phase is then responsible for the bulk of the type checking work.

=== Lowering and Desugaring <subsection-impl-type-checking-lowering-and-desugaring>

This initial phase has two primary functions, namely

+ it must _completely_ lower type declarations, and;
+ it must lower _only_ the type signatures of term declarations.

The resulting #short("ir") is defined in the `ast::typed` module, and is quite similar to the #short("ir") defined in `ast::bound`; the largest difference is the inclusion of the `ast::typed::Ty` struct and its corresponding annotation form `ast::typed::Typed`.

#let __impl_tc_ty_definition = {
  ```rust
  struct Ty<V> {
    vars: HashSet<V>,
    matrix: Arc<TyMatrix<V>>,
  }

  enum TyMatrix<V> {
    Prim(PrimTy),
    Var(V),
    Tuple(Box<[Arc<Self>]>),
    Adt {
      name: TypeId,
      args: Box<[Arc<Self>]>,
    },
    Fn {
      domain: Box<[Arc<Self>]>,
      codomain : Arc<Self>,
    },
  }
  ```
}

#shortcolumns(
  [
    Since Jabber's type system is predicative, every type can be written in prenex normal form. It is for this reason that the `Ty` and `TyMatrix` types are distinguished, since a `TyMatrix` represents only the unquantified _matrix_ of the full type.
    #footnote[The terms _prefix_ and _matrix_ were borrowed from first-order logic, where they are part of the definition of the prenex normal form.]

    If a type variable appears in the `vars` field of a `Ty` then it is universally quantified; otherwise it is an existentially quantified unification variable. In the language of ML type systems, `TyMatrix` represents a @monotype, whereas `Ty` represents a @polytype.

    Both representations are held behind atomically reference-counted smart pointers (`std::sync::Arc`), since they are frequently cloned during the full type checking algorithm.
  ],
  [
    #figure(
      caption: [The definitions of `Ty` and `TyMatrix` from `jabber_core::ast::typed`.],
      __impl_tc_ty_definition,
    )
  ],
)

The first portion of this phase begins by sweeping over the type declarations and processing them according to their kinds.

- #short("adt") declarations are lowered to `ast::typed::Adt`, where their non-record constructors are given types. Unit constructors receive plain `TyMatrix::Named` types, whereas tuple constructors are typed as `TyMatrix::Fn` with the codomain corresponding to the appropriate `TyMatrix::Named` type.
- Type alias declarations are preprocessed to make normalising them easier during full type checking, but are otherwise unaltered.
- External type declarations are opaque from the perspective of the compiler, and so cannot be meaningfully processed.

Term declarations are also visited, but only the types of their signatures are processed. This information is necessary in the next phase, where the bodies of the term declarations are typechecked and lowered completely. As a precursor to full type checking, the lowering pass also emits an error for every public function or constant declaration whose type contains existential type variables. This is to comply with the rule that public interfaces must be concrete, and hence that the scope of type inference is constrained to at most a single module.

=== Type Checking and Type Inference <subsection-impl-type-checking-type-checking-and-type-inference>
We now turn to the primary typechecking phase, which implements _bidirectional typing_, a form of type checking that counterposes type checking and type inference to provide better error messages and handle undecidable type system features more gracefully @bidirectional-typing-dunfield-krishnaswami.

As described in @bidirectional-typing-dunfield-krishnaswami and @complete-and-easy-bidirectional-typechecking, bidirectional typing consists of two
#footnote[The algorithm in @complete-and-easy-bidirectional-typechecking actually has _three_ modes, but the third mode can be seen as a special case of the second and is omitted here. Since Jabber doesn't have higher-rank polymorphism, this omission doesn't cause any problems or restrictions.]
_typing modes,_ which are distinguished by whether they consider types to be inputs or outputs.
+ In the _checking_ mode, the input term is checked against an input type.
+ In the _inferring_ mode, the input term yields an output type.

When implemented in actual code, these typing rules are the `check` and `infer` methods of the `env::typed::Typer` type respectively; they are mutually recursive functions that rely on shared implicit state managed by their `Typer` receiver (@figure-typer-definition).

#align(center)[
  #figure(
    caption: [The definition of `env::typed::Typer`.],
    ```rust
    pub struct Typer<'a> {
        types: &'a [lower::LoweredType<Uid>],
        list_id: TypeId,
        term_types: &'a lower::TermTypeMap<Uid>,
        errors: &'a mut Vec<TypingError>,
        unifier: UnificationTable<InPlace<TyVar>>,
        var_assignments: HashMap<TyVar, Arc<TyMatrix<TyVar>>>,
        uid_assigments: HashMap<Uid, TyVar>,
        local_var_types: HashMap<Uid, Arc<Ty<TyVar>>>,
        current_module: ModId,
    }
    ```,
  ) <figure-typer-definition>
]

Each kind of expression is associated with one of the two modes, though the majority are handled in the inferring mode; in fact the _only_ expressions associated with the checking mode are lambda expressions, since it is not possible to infer their types without additional context. The `check` and `infer` functions can still accept any expression, but each will invoke the other if it encounters an expression that doesn't belong to its mode.

For most expressions, typechecking is relatively simple in this architecture: they are passed to `Typer::infer` as the entrypoint, where the function branches on the expression kind and attempts to infer the type of the expression. This process usually recurses on the inner expressions (e.g. the fields of record constructor expressions, the elements of list expressions, or the statements of block expressions), with literals and names as the terminal non-recursive cases. The types of literals can be trivially inferred, whereas names must first be looked up in the environment.

But what if a name doesn't yet have an associated type in the environment? In these cases a fresh unbound type variable is produced with the `Typer::fresh_var` method and added to the environment, where it can then be obtained in future look ups. This type variable represents some unknown type, to be determined later in the type checking process.

=== Unification

An essential part of type checking is handling cases where two types should be the same type. For example, checking the type of a call expression requires checking that the types of the arguments match the domain of the function type.

For simple cases, this can be handled by checking equality of types. It is obvious that `int` and `float` are not the same type, and it is likewise mundane to say that `()` and `()` are the same type. But the introduction of variables makes this concept more complex: for example, given the type variables `a` and `b`, are the types `a -> b` and `b -> a` the same? The question ceases to be meaningful, because it is contingent on the values of the variables.

Conversely, if we judge that `a -> b` and `b -> a` should be the same type, it must follow that `a` and `b` should be the same type. That is, the judgement `a -> b ≡ b -> a` is not a simple boolean-valued statement, but a computation with a side effect on the variables involved.

The operation that performs the required boolean check while handling these potential variable side effects is called _unification;_ in the theoretical sense it is responsible for computing sets of substitutions that make two types equal, if such a set exists at all @tapl[§22.4]. In our implementation it also then _applies_ those substitutions and modifies the implicit state accordingly.

Unification is implemented with the `Typer::unify_matrices` method, which takes two type matrices and unifies them, returning an error if this is not possible; the following rules are used:
- primitive types other than `!` unify successfully only if they are equal;
- given any other type, `!` will coerce into that type;
- two variables unify into the same variable;
- a variable and a non-variable value are unified by assigning the value to the variable, though this is only permissible if the variable does not occur in the value; #footnote[If this check was omitted, it would be possible to construct infinitely large types; for example assigning to the variable `a` the function type `a -> a` would create an infinitely long function type `a -> a -> ⋯ -> a`.]
- two tuples unify recursively, but only if they have the same length;
- likewise two functions unify recursively only if their domains have the same arity; #footnote[There is a special case for functions whose domain is nullary or `()`, which are both coerced to have the unit domain. Their codomains are unified as normal.]
- named types must have the same name and number of arguments, and then their arguments can be unified recursively.

For memory efficiency reasons, variable-variable unification is tracked with a @union-find data structure from the `ena` crate that can efficiently compute the representative members of equivalence classes of variables. When type checking is complete, all remaining type variables are replaced with their representative elements from this structure in a process called _zonking_.

=== Let Generalisation

A standard feature of @ml\-family type systems is _let generalisation,_ a rule that dictates how the type variables in an expression on the right hand side of a `let` statement should be bound. In the broadest sense, it provides that the type variables of a subject expression should be universally bound when it is placed within a `let` statement.

#let __impl_ty_let_gen_example = [
  #figure(
    caption: [An example program involving let generalisation in Jabber.],
    ```jabber
    // the return type is redundant here
    fn let_gen() -> (bool, int) = {
      let f = x -> x;
      (f(false), f(7))
    }
    ```,
  ) <figure-let-gen-example>
]

#shortcolumns(
  [
    Consider an example: in @figure-let-gen-example, the type checker will first infer the type `a -> a` for the expression `x -> x`, with `a` unbound. When it is bound to `f`, that type becomes `∀a. a -> a`, and then it is instantiated twice in the tuple expression with `a = bool` and `a = int`.
  ],
  __impl_ty_let_gen_example,
)

In the compiler, let generalisation is implemented as a special case in the `Expr::Block` branch of `Typer::infer`. Despite being a relatively small element of the overall type system, it was an unusually large source of errors during development; there are a number of edge cases where, unless it is guarded against, the type checker can overgeneralise the subject type and miscompile the program as a result.


=== Remarks

The most obvious omission from this portion of the compiler is any kind of pattern checking, a ubiquitous feature among similar languages. This was a practical consequence of the time constraints, as pattern matching is a relatively involved and complicated process.
#footnote[It's fairly common knowledge within the Rust community that pattern exhaustiveness analysis is NP-hard, as demonstrated in a well-known blog post by a `rustc` contributor @compiler-crimes-pattern-exhaustiveness-is-np-hard.] As a consequence, the compiler is not a completely type-safe implementation of Jabber as designed in @chapter-design, and requires additional work to achieve such a standard.

Additionally, there is a subtle issue related to let generalisation that was not discovered until the very end of the project, caused by a failure to implement a feature called the _value restriction_. In essence, the compiler should not be permitted to generalise types if they contain mutable record fields. The instances of such types do not qualify as syntactic values, and so it is possible to overgeneralise them and cause miscompilations @tapl[§22.7].

== Code Generation <section-impl-codegen>

The entire backend of the compiler is implemented by this stage; it is responsible for lowering, generating, and rendering executable artifacts. In particular, these artifacts are `.rkt` files containing #short("r6rs") #short("scheme") code.

=== Lowered Representation <subsection-impl-codegen-lowered-representation>

Before executables can be generated, we need to convert the results of the type checking stage into an #short("ir") that more closely resembles the target language; this representation is defined in the `codegen::scm` module.

#let __impl_cg_scm_expr_definition = {
  ```rust
  pub enum Expr {
    Call {
      callee: Box<Self>,
      args: Box<[Self]>,
    },
    Lambda {
      args: Box<[Symbol]>,
      body: Box<Self>,
    },
    Match {
      scrutinee: Box<Self>,
      arms: Box<[MatchArm]>,
    },
    MatchLetSeq {
      bindings: Box<[(Pattern, Self)]>,
      body: Box<Self>,
    },
    MatchLambdaVariadic {
      patterns: Box<[Pattern]>,
      body: Box<Self>,
    },
    Literal(Literal),
    Builtin(Builtin),
    Symbol(Symbol),
  }
  ```
}

#let __impl_cg_scm_expr_lhs = [
  `scm::Expr` is the primary type in the #short("ir"), and corresponds directly to an expression of #short("r6rs") #short("scheme")\; each variant represents a particular language element.

  The majority of the variants denote intrinsic language elements: `Lambda` corresponds to the `lambda` form defined in the #short("r6rs") standard @r6rs-report[§11.4.2], whereas the `Call`, `Symbol`, and `Literal` variants correspond to the primitive literal, variable reference, and procedure call syntax respectively @r6rs-report[§9.1].

  When the compiler needs to assume the existence of particular definitions, it does so using the `Builtin` variant; this effectively provides a set of presumed-extant names.

  `Match`, `MatchLetSeq`, and `MatchLambdaVariadic` are the most exotic variants, as they correspond to the `match`, `match-let*`, and `match-lambda**` forms from Racket's `racket/match` library respectively. They exist largely only to simplify the process of compiling binding patterns.
]

#let __impl_cg_scm_expr_figure = [#figure(
    caption: [The definition of `codegen::scm::Expr`.],
    __impl_cg_scm_expr_definition,
  ) <figure-scm-expr-definition>]

#shortcolumns(
  __impl_cg_scm_expr_lhs,
  __impl_cg_scm_expr_figure,
)

Also defined in `codegen::scm` are the `MatchArm`, `Pattern`, `Literal`, and `Builtin` types mentioned in @figure-scm-expr-definition; these denote language elements that are not necessarily expressions. For example, both `Expr` and `Pattern` have `Literal` variants because literals may appear as both expressions and patterns; similarly match arms may only appear within the `Match` variant and so are explicitly distinguished as a separate type.

#align(center)[
  #figure(
    caption: [The definitions of `MatchArm` and `Pattern` from `codegen::scm`.],
    ```rust
    /// An individual match arm.
    pub struct MatchArm<A = Expr> {
        pub pattern: Pattern,
        pub body: A,
    }

    /// A subset of the racket/match pattern grammar.
    pub enum Pattern {
        Wildcard,
        Literal(Literal),
        Ident(Symbol),
        Cons {
          head: Box<Self>,
          tail: Box<Self>
        },
        Boxed(Box<Self>),
        List(Box<[Self]>),
        Vector(Box<[Self]>),
    }
    ```,
  )
]

=== Package Lowering <subsection-impl-codegen-package-lowering>

Each Jabber package is lowered independently to an #short("r6rs") `library` form @r6rs-report[§7.1], effectively being flattened into a list of definitions and a set of imports and exports. This flattened form is defined by the `codegen::lower::LoweredPackage` type (@figure-lowered-package-definition), which divides the definitions into four sequential groups: _externals_, _type constructors_, _functions_, and _constants_.

#let __impl_cg_lowered_package_definition = [
  #figure(
    caption: [The `Def` and `LoweredPackage` types as defined in `codegen::lower`.],
    ```rust
    /// A `(define <name> <value>)` form.
    pub struct Def<T> {
      pub module: ModId,
      pub name: Blamed<Symbol>,
      pub value: T,
    }

    /// The lowered contents of an
    /// individual package.
    pub struct LoweredPackage {
      pub name: Symbol,
      pub imports: Vec<Symbol>,
      pub exports: Vec<Symbol>,
      pub externals: Vec<Def<Symbol>>,
      pub constrs: Vec<Def<Blamed<Expr>>>,
      pub functions: Vec<Def<Blamed<Expr>>>,
      pub constants: Vec<Def<Blamed<Expr>>>,
    }
    ```,
  ) <figure-lowered-package-definition>
]

#let __impl_cg_example_lowered_package_scheme = [
  #figure(
    caption: [An example of a rendered Jabber library package.],
    ```scm
    (library (example)
      (import
        (support support)
        (target core))
      (export
        example/helloworld
        example/HELLO)

      ;; externals
      (define __prim_print displayln)

      ;; functions
      (define (example/helloworld)
        (__prim_print example/HELLO))

      ;; constants
      (define example/HELLO
        "hello, world!"))
    ```,
  ) <figure-example-lowered-package>
]

#shortcolumns(
  __impl_cg_lowered_package_definition,
  __impl_cg_example_lowered_package_scheme,
)

The lowering process is managed by a `codegen::lower::Lowerer` instance (@figure-codegen-lowerer-definition), which collects and persists information across method invocations; it is also used to memoise potentially expensive functions used during lowering.

#align(center)[
  #figure(
    caption: [The definition of `codegen::lower::Lowerer`.],
    ```rust
    pub struct Lowerer<'a> {
        env: &'a mut TypedEnv,
        canonical_term_names: HashMap<TermId, Symbol>,
        canonical_constr_names: HashMap<TyConstrIndex, Symbol>,
        named_type_shapes: HashMap<TypeId, Shape>,
        type_constr_definitions: HashMap<TyConstrIndex, Def<Blamed<Expr>>>,
        field_orders: HashMap<TyConstrIndex, Box<[Symbol]>>,
        scheme_symbol: Symbol,
    }
    ```,
  ) <figure-codegen-lowerer-definition>
]

Each package is lowered by invoking the `Lowerer::lower_package` method, which causes the `Lowerer` to compute the set of definitions in the package and invoke the `Lowerer::lower_term` method on each of them.

The terms are then processed according to their kind, where
+ external function definitions are rendered to `Def<Symbol>` instances by retrieving the `Symbol` associated with their `@external.scheme` attributes;
+ constant definitions are rendered to `Def<Blamed<Expr>>` instances by lowering their right-hand values with `Lowerer::lower_expr`;
+ function definitions are render to `Def<Blamed<Expr>>` instances by lowering their bodies with `Lowerer::lower_expr` and their parameters with `Lowerer::lower_params`.

Expressions are lowered in a fairly conventional way, but a few specific kinds of expression are worth remarking on in particular.

- Block expressions are lowered to `match-let*` forms, represented by `Expr::MatchLetSeq`, which differs from the standard `let` form by allowing variable binding patterns. The asterisk is meant to evoke the `let*` form, because both forms allow later bindings to refer to earlier bindings @the-racket-reference[§9.1].

- Record and tuple constructor expressions are lowered differently based on the runtime representations of their types; these representations are computed by the `Lowerer::shape_of_named_type` method (@subsection-impl-codegen-shape-analysis). The same shape analysis also affects the lowered forms of tuple and record field expressions, as well as the built-in mutation (`<-`) operator.

- All non-local identifiers are _canonicalised_ by qualifying them with their absolute paths and joining those identifiers with the forward slash character. #footnote[This is actually a way to guarantee canonical names never collide, since the forward slash cannot occur in Jabber identifiers.] For example, the `List.Cons` constructor is canonicalised as `core/list/List/Cons`, and since package names must be globally unique this guarantees that no other definition will ever have this name.

When function definitions and lambda expressions are processed, their body expressions and parameter patterns are lowered independently before being assembled into a single `Expr::MatchLambdaVariadic` instance.

The patterns which occur in function parameters, lambda parameters, match expressions, and let statements are lowered to the pattern DSL defined by `racket/match` @the-racket-reference[§9] by `Lowerer::lower_pattern`. As with expressions, some patterns require shape analysis to be lowered correctly; these are the unit, tuple, and record constructor patterns.

=== Shape Analysis <subsection-impl-codegen-shape-analysis>

In order to lower certain kinds of expressions and patterns, we need to know how the relevant types will be represented at runtime. This representation is called a _shape_ in the compiler, and is defined by the `codegen::repr::Shape` type.

#let __impl_cg_shape_definition = [
  #figure(
    caption: [The definitions of `repr::Shape` and `repr::Variant`.],
    ```rust
    pub enum Shape {
      Prim(ast::typed::PrimTy),
      MutBox,
      List,
      Option,
      Extern { name: TypeId },
      Fn { arity: usize },
      Struct { arity: usize },
      Variants(Box<[Variant]>),
    }

    pub enum Variant {
      Cons,
      Ref,
      Plain { arity: usize },
    }
    ```,
  ) <figure-repr-shape-definition>
]

#shortcolumns(
  [
    Shape analysis could be arbitrarily complex, but we abide by the general principle that the shape of a type should be a discriminated set of `Variants` unless we can show that a more precise shape would work.

    The `Prim`, `Extern`, and `Fn` shapes are special markers for values that have an obvious #short("scheme") representation, while `MutBox`, `List`, and `Option` describe the shapes of types which are isomorphic to the `Ref`, `List`, and `Option` types defined in Jabber's `core` library. The `Struct` shape is a special case of `Variants` with only a single constructor, and hence doesn't need a discriminant field.
  ],
  __impl_cg_shape_definition,
)

Uninhabited types like `!` do not and cannot have runtime representations; their shape in the compiler is `Shape::Prim(PrimTy::Never)`. The process of typechecking guarantees that uninhabited types cannot be values at runtime.

When rendered, each shape is mapped to #short("scheme") as follows:
- `()` becomes `(void)`.
- `bool` becomes `#t` or `#f`.
- `int` becomes an exact number @r6rs-report[§3.2].
- `float` becomes a `flonum` @r6rs-report[§3.3].
- `char` and `string` correspond to the #short("scheme") character and string types.
- `MutBox` corresponds to the box type, and allows the use of `set-box!` for mutation.
- `List` corresponds directly to the list type.
- `Option` has the constructors `#f` and `box`, corresponding to `None` and `Some`. Unlike `MutBox`, the box constructor is semantically immutable.
- `Extern` and `Fn` are opaque in Jabber, so are mapped to values of no specific type.
- `Struct` corresponds to a vector with a fixed arity.
- `Variants` corresponds to a vector with a variable arity, and whose first field is a discriminant. The discriminants are symbols corresponding to the names of the constructors.

This analysis is a very basic kind of optimisation, and more complex implementations might emphasize overall type structure instead of simple constructor analysis. Still, it helps to reduce unnecessary memory overhead by eliding redundant discriminants and provides special cases for some of the most commonly used types.

=== Rendering <subsection-impl-codegen-rendering>

Given a `LoweredPackage`, the very last task of the compiler is to render the package into a Scheme program. The generic interface for this functionality is the `codegen::ToDoc` trait, which converts its receiver into an abstract document represented by the `pretty::RcDoc` type. #footnote[`RcDoc` is a reference-counted wrapper over the actual `pretty::Doc` type, which is used here to reduce the cost incurred by frequently cloning portions of documents.]

#let __impl_ren_to_doc_definition = [
  #figure(
    caption: [The definition of `codegen::ToDoc`.],
    ```rust
    pub trait ToDoc {
      fn to_doc(
        self,
        interner: &mut StringInterner,
      ) -> RcDoc<'static, ()>;
    }

    impl ToDoc for Pattern { /**/ }
    impl ToDoc for Expr { /**/ }
    impl ToDoc for LoweredPackage { /**/ }
    impl<T> ToDoc for Def<T>
      where T: ToDoc, { /**/ }
    ```,
  ) <figure-to-doc-trait-definition>
]

#shortcolumns(
  [
    Any type can indicate that it can be rendered by implementing the `ToDoc` trait, which a caller can then use by invoking the `to_doc` method; this requires access to a `StringInterner` in order to convert from `Symbol` values back into strings.

    The implementations of `ToDoc` for `Expr`, `Pattern`, `LoweredPackage`, etc. are mutually recursive, and for `Def` it is also inductive: `Def<T>` implements `ToDoc` if and only if `T` implements `ToDoc`.
  ],
  __impl_ren_to_doc_definition,
)

Because `ToDoc::to_doc` returns an abstract document type rather than a concrete string, each implementer also makes use of the utilities provided by `pretty` to describe how it should be formatted within the context of the overall document. Take as an example the implementation of `ToDoc` for `Def<T>` (@figure-to-doc-def-impl-definition), which should be rendered as a #short("scheme") `define` form.

#align(center)[
  #figure(
    caption: [The implementation of `ToDoc` for `codegen::lower::Def`.],
    ```rust
    impl<T: ToDoc> ToDoc for lower::Def<T>
    where
      T: ToDoc,
    {
        fn to_doc(self, interner: &mut StringInterner) -> RcDoc<'static, ()> {
            // resolve the bound identifier
            let name = RcDoc::as_string(interner.resolve(self.name.item).unwrap());
            // recursively lower the bound value
            let value = self.value.to_doc(interner);

            // construct and return the document
            RcDoc::text("(")
                .append(RcDoc::text("define"))
                .append(RcDoc::space())
                .append(name)
                .append(RcDoc::softline())
                .append(value)
                .append(RcDoc::text(")"))
        }
    }
    ```,
  ) <figure-to-doc-def-impl-definition>
]

The entire form is fractured into its constituent elements, with contextual whitespace inserted in the appropriate places. The `RcDoc::space` combinator denotes a mandatory space character be inserted between the `define` identifier and the `name` field, while the `RcDoc::softline` combinator allows the layout engine to decide between using a newline or space character as necessary.

All the implementations of `ToDoc` provide similar context-sensitive formatting rules, with the result being a relatively human-legible #short("scheme") program when the documents are printed to strings. This process is not perfect, however, and frequently produces worse results when compared to dedicated #short("scheme") formatting tools.


== Runtime Support <section-impl-runtime-support>

#short("r6rs") #short("scheme") is a very minimal language; indeed the core language does not include the `define` and `lambda` forms! These are instead provided by the `(rnrs base (6))` library @r6rs-report[§11]. Conversely, much of the functionality other languages might consider essential is instead provided by a set of auxiliary libraries, including basic IO utilities and arithmetic operators @r6rs-libs-report[§8, §11].

To address this, the compiler includes a runtime support library in `support/support.rkt` #footnote[This naming convention is borrowed from @idris2, which uses a similar system of support files for its various backends.] that provides the essential definitions used by almost every Jabber program.

#align(center)[
  #figure(
    caption: [The `export` section of `support/support.rkt`.],
    ```scm
    (library (support)
      (export
        define lambda quote quasiquote void equal?  ; essentials
        and or                                      ; lazy and/or
        + - * / expt mod div*                       ; arithmetic
        < <= > >=                                   ; comparisons
        fl+ fl- fl* fl/ flexpt                      ; float arithmetic
        fl<? fl<=? fl>? fl>=?                       ; float comparisons
        not xor strict-binary-and strict-binary-or  ; bools
        length append map cons                      ; lists
        vector vector-ref vector-set!               ; vectors
        string-length string-append substring*      ; strings
        match match-let* match-lambda**             ; pattern matching
        box box? unbox set-box!                     ; reference cells
        println                                     ; IO
        panic! panic-with-msg! unreachable! todo!   ; panics
        number->string)                             ; formatting
    ```,
  ) <figure-support-exports>
]

Most of the definitions provided by the support library (@figure-support-exports) are essentially reexports of standard forms from the #short("r6rs") base and auxiliary libraries, which are generally available across all major #short("r6rs") #short("scheme") implementations. Another small set of definitions are simple wrappers defined by the support library itself; these include `div*`, `substring*`, the strict binary operators, and the panicking functions.

#let __impl_rt_support_content = [
  #figure(
    caption: [The definitions of the `div*` and `substring*` forms in the support library.],
    ```scm
    (define (div* lhs rhs)
      (if (zero? rhs)
        #e0
        (div lhs rhs)))

    (define (substring* str start end)
      (guard)
        (err ((string)))
        (substring str start end))
    ```,
  ) <figure-support-definitions>
]

#shortcolumns(
  [
    The forms suffixed with an asterisk exist to prevent runtime exceptions from occurring; recall that Jabber does not have a notion of exceptions and must either panic or continue instead.

    `div*` and `substring*` follow some common conventions for languages without exceptions: division by 0 is defined to be 0, while invalid substring indices result in the empty string. This convention is used by @gleam, among others.
  ],
  __impl_rt_support_content,
)

But a portion of these definitions are non-portable: they are not available on all compliant #short("r6rs") implementations. These are the box (`box`, `box?`, `unbox`, `set-box!`) and pattern matching (`match`, `match-let*`, `match-lambda**`) forms, which are reexported from @racket's `racket/base` and `racket/match` libraries respectively. #footnote[@racket actually shares the box functions with @chez, since the primary @racket implementation is built on a fork of @chez.] This is the reason that the compiler doesn't just use whatever #short("scheme") implementation happens to be available on the host system, since it can't guarantee that that implementation will be properly configured.

== Interface <section-impl-interface>

The interface consists of two distinct elements:
+ An argument parser and preprocessor, defined in the `cli` module.
+ The underlying driver that invokes the compiler, defined in the `driver` module.

These are effectively the front and back ends of the interface, with the `cli` module also responsible for printing help messages, reporting the compiler version, and otherwise behaving as is expected of a command line program.

#let __impl_interface_cli_definition = [
  #figure(
    caption: [The definition of `cli::Command`.],
    ```rust
    #[derive(Subcommand)]
    pub enum Command {
        Compile {
            #[arg(short = 'i', long)]
            input: Option<Box<Path>>,
            #[arg(short = 'o', long)]
            output_dir: Option<Box<Path>>,
        },
        Run {
            #[arg(short = 's', long)]
            support_path: Box<Path>,
            #[arg(short = 'i', long)]
            input: Option<Box<Path>>,
            #[arg(short = 'o', long)]
            output_dir: Option<Box<Path>>,
        },
    }
    ```,
  ) <figure-cli-interface-command-defn>
]

#shortcolumns(
  [

    For the front end, the `clap` crate was used to automatically generate and preprocess the arguments. The entrypoint for the interface was defined in the `cli::Cli` type, with subcommands defined in `cli::Command` (@figure-cli-interface-command-defn).

    When the compiler is invoked, it first runs the `cli::Cli::parse` function on the arguments to get a `cli::Cli` instance, exiting with an error message if anything goes wrong.

    Some light additional processing is done in the root `interface` method to construct a `driver::Context` instance, at which point it branches on the subcommand and invokes a function from the `driver` module.

  ],
  __impl_interface_cli_definition,
)

The `driver` module is effectively a library of functions implementing the interface's back end, and is centralised around three primary types—`driver::Context`, `driver::Error`, and `driver::Result`—which serve as the principal inputs and outputs of the #short("api").

#let __impl_interface_driver_types_definition = [
  #figure(
    caption: [
      The `Result`, `Error`, and `Context` types from the `driver` module.
      #footnote[The `thiserror` annotations on `Error` have been omitted here for brevity.]
    ],
    ```rust
    pub type Result<T = ()>
      = std::result::Result<T, Error>;

    pub enum Error {
        CouldNotFindRacketBinary,
        Io(std::io::Error),
        MetadataLoad(MetadataLoadError),
        PackageLoad(PackageLoadError),
        DependencyCycle(Box<str>),
    }

    pub struct Context {
        pub libs_root: Box<Path>,
        pub racket_bin: Box<Path>,
    }
    ```,
  )
]

#shortcolumns(
  [
    The `Context` type represents the arguments common to all compiler functionality, and most of the primary invocation functions are presented in the #short("api") as methods of `Context`; it is the primary input type.

    Whereas `Context` is an input of the `driver` #short("api"), the `Result` and `Error` types are its outputs; almost every function and method returns some form of `driver::Result<T>`. The design pattern of local versions of `result::Result` is very common in @rust, including in its standard library. `Error` is simply a sum of all the possible error types that might occur from a `driver` function, and presents a single type from which to implement user-facing error messages.
  ],
  __impl_interface_driver_types_definition,
)

At invocation, each of the `cli::Command` variants is mapped to a method of `Context`:
- `Command::Compile` corresponds to `Context::compile_package`.
- `Command::Run` corresponds to `Context::execute_binary_package`.

The `compile_package` method compiles a root package at the given path and writes the resulting artifacts to a given output directory, defaulting to a subdirectory of the package root with the name `target`. Dependencies of the root package are resolved by searching for them in the path given by the `libs_root` field of `Context`, which is assumed to be a flat directory of Jabber library packages. This method is also responsible for detecting and reporting cycles in the dependency graph, using the `petgraph` crate to build and traverse this graph before compilation to produce a topological ordering of the required packages.

If the root package is a binary package, then this method also generates a short stub file called `0thunk.rkt` which just loads the package and calls its `main` function; the number at the beginning of its name is a simple trick to prevent collisions with the names of Jabber modules, since `0thunk` is not a legal identifier.

Executing a binary package is a simpler operation, implemented in about 80 lines of @rust. The `execute_binary_package` method (@figure-execute-binary-package-defn) first checks if the given package is actually a binary package according to its metadata file, and compiles it to an output directory if that check passes. It then invokes the given @racket program with the appropriate command line arguments and the path to the package's `0thunk.rkt` file, printing the results after @racket exits.

#let __impl_driver_execute_bin_impl = [
  #figure(
    caption: [The definition of `driver::Context::execute_binary_package`.],
    ```rust
    impl Context {
        pub fn execute_binary_package(
            &self,
            package_root: &Path,
            output_dir: &Path,
            support_path: &Path,
        ) -> Result {
            let (md, _) = load_package_with_metadata(package_root)?;
            if md.package.kind == PackageKind::Library {
                panic!("tried to run a library package")
            }

            self.compile_package(package_root, output_dir)?;

            let mut racket = Command::new(self.racket_bin.to_path_buf());
            let cmd = racket
                .arg("--search")
                .arg(package_root)
                .arg("--search")
                .arg(support_path.parent().unwrap())
                .arg(output_dir.join(THUNK_FILE_NAME));

            let output = cmd.output()?;
            std::io::stdout().write_all(&output.stdout)?;
            Ok(())
        }
    }
    ```,
  ) <figure-execute-binary-package-defn>
]

#align(center)[#__impl_driver_execute_bin_impl]

When it is invoked, @racket is provided with two extra paths in which to search for modules to load; these are the `support_path`
#footnote[Actually, the parent directory of the support path. @r6rs libraries expect to belong to a collection, which in this case is `support`, but in the interface it makes more sense to pass `-s <parent>/support` instead of `-s <parent>`.]
and `libs_path`. This module loading mechanism is how the compiled dependencies are imported by the root package using them, so @racket needs to know where they're located. However we don't tell @racket that it needs to use the @r6rs language module, since this can be inferred from the `#!r6rs` header in the artifact files themselves.


== Testing <section-impl-testing>

There are three kinds of tests used to verify the proper behaviour of the compiler:
1. #short("tree-sitter") corpus tests (in `/tree-sitter-jabber/test/corpus`).
2. Conventional unit tests within the compiler itself, written in @rust.
3. Full package compilation tests (in `/tests`).

The #short("tree-sitter") corpus tests are a collection of Jabber programs with their expected outputs, and are used to verify that the generated parser behaves as expected on a representative sample of inputs @tree-sitter-documentation[§2.5].

#let __impl_testing_treesitter_test_example = [
  #figure(
    caption: [An example of a @tree-sitter corpus test from `test/corpus/operators.txt`.],
    ```
    ==============
    cons operator
    ==============

    const zeros = 0 :: 0 :: 0 :: []

    ------------------------------------

    (source_file
      declaration: (declaration
        body: (const_decl
          name: (ident)
          value: (binary_expr
            lhs: (dec_literal)
            operator: (binary_operator)
            rhs: (binary_expr
              lhs: (dec_literal)
              operator: (binary_operator)
              rhs: (binary_expr
                lhs: (dec_literal)
                operator: (binary_operator)
                rhs: (list_expr)))))))
    ```,
  )
]

#shortcolumns(
  [
    Each @tree-sitter corpus test has three elements, in the following order:

    + A name enclosed with delimiter lines.
    + A fragment of Jabber code.
    + The expected parse tree of the Jabber code, written as an S-expression and annotated with field names.

    There are nearly 60 such tests spread among 13 files, with each file focused on a particular grammar element or group of elements.

    During development, frequent changes to the parser were made to its implementation, to improve its output and address some errors encountered in certain pathological edge cases.

    Whenever a change was made, the entire corpus was run to determine if any regressions had been introduced; each time this occurred new tests were also introduced to improve the total coverage of the test suite.

  ],
  __impl_testing_treesitter_test_example,
)

The conventional unit tests are distributed throughout the compiler, implemented as @rust functions marked with the ```rust #[test]``` attribute, and can be processed and evaluated in bulk with the `cargo test` command. Most of these tests (about 80%) are extremely local, verifying particular properties of particular types; for example `unique::tests::id_uniqueness` checks the uniqueness properties of several sequential calls to `unique::Uid::fresh`, whereas `literal::tests::string_escapes` runs the `literal::string_contents` parser function on each of the string escape sequences and checks the resulting outputs. #footnote[Even though these tests are defined in submodules called `tests`, by convention they are located at the bottom of the relevant files rather than in their own separate files.]

A small group of the unit tests (the remaining 20%) are responsible for testing the sequential compiler stages, and have a common format: each test first loads the `core` library from `/libs/core`, and applies the preceding compiler stages to it until it reaches the stage being tested. They then diverge, checking particular properties of each stage and emitting debugging information as they go. The best example of this is `env::typed::tests::build_lowered_env_from_core`, which compiles `core` up to the typechecking stage, debugs information about the types of items in the `core.ref` module, and then exits.

Lastly, the `/tests` directory contains a collection of entire Jabber packages that the complete compiler can be tested against; for example `/tests/hello_world` is an extremely simple binary Jabber package that just prints `hello, world!` to the terminal. These full package compilation tests are the final threshold for compiler testing, and serve the role of integration tests; each is designed to test multiple languages features simultaneously and in combination.

= Evaluation <chapter-evaluation>

#quote(attribution: [_Jabberwocky_ by Lewis Carroll, 1871])[
  One, two! One, two! And through and through\
  The vorpal blade went snicker-snack!\
  He left it dead, and with its head\
  He went galumphing back.
]

Languages are sometimes contentious objects, and arguments about them are famously never-ending. This is doubly true for functional languages, where opinions are strongly held as to which philosophies of functional programming ought to win out.

We cannot objectively evaluate a language—there is no universal standard by which to do so. It would clearly be pointless to compare @python and @haskell on the same basis, when they articulate such vastly different objectives and philosophies. But it _is_ possible to compare a language's design and implementation with its stated goals, and to arrive at a sensible contextual evaluation in that framing.

This chapter will focus on a critical evaluation of Jabber, its design, and the implementation of its compiler. That is, it will especially focus on those areas most out of alignment with the objectives and philosophy of the language; we presume that laudatory remarks can be safely omitted here at little expense.

== Philosophy and Objectives

Recall that in earlier chapters, several different objectives were outlined for Jabber's design. Among these were

+ _simplicity_—that Jabber should be relatively small and easy to learn.
+ _immutability_—that Jabber should lend itself to programs with as little mutable state as possible.
+ _consensus_—that Jabber should defer to the majority position of its peers whenever it is sensible to do so.

Taken together, these premises articulate a fairly conventional design philosophy: Jabber should be a simple, conventional functional language that lends itself well to purely functional, immutable programs. Notice that this philosophy somewhat conflates syntactic and semantic concerns, which reflects the view that the two domains are inherently dependent on one another.

Other secondary objectives, though left implicit in the design, are nonetheless useful in a holistic analysis of Jabber; these are

- _consistency_—the language should be internally consistent in its syntax and semantics.
- _orthogonality_—language features should have as little overlap as possible, and there should be exactly one obvious way to write a given expression.
- _practicability_—it must be possible to use the language for any given task without an unreasonable degree of effort.

== Syntax <section-evaluation-syntax>

Jabber's syntax began with a design very similar to @rust's, and has drifted away from it as its overall design evolved. As a result, there are some almost _vestigial_ elements in the grammar that make much less sense in Jabber than they do in Rust.

#let __eval_jbr_vestigial_syntax = [
  #figure(
    caption: [Examples of the vestigial elements in Jabber's syntax.],
    ```jabber
    fn direct_block() {
      // ...
    }

    fn explode() = if true {
        panic()
    }

    fn tuple_indices() -> char = {
      let tup = (1, true, 'c');
      tup.2
    }
    ```,
  )
]

#shortcolumns(
  [
    An obvious example of such vestigial syntax is the implicit block body rule for function declarations, which allows them to omit the equals sign between their signatures and bodies if the body expression is a block.

    The conditional if-else expression is another example, as it can always be replaced with an equivalent match expression.

    Similarly, the tuple indexing syntax was carried over wholesale from @rust, even though it quite clearly overlaps with pattern matching features.
  ],
  __eval_jbr_vestigial_syntax,
)

Conversely, experience with Jabber has made it apparent that it lacks some syntactic niceties when compared with peer languages. In particular, the idiom of a unary function whose body is a match expression on its argument is so common in functional languages that many languages have dedicated syntax for defining functions of this kind; in @ocaml it is the `function` keyword, while in @racket it is the `match-lambda` form.

To be sure, most of Jabber's syntax meets the outlined design goals: every language element is attested by at least one other language, often several, with a general bias towards the simpler syntactic choices. It is only these vestigial components that are notably out of place, and the language would be better served by redesigning or entirely removing them.

== Implementation

The issues identified in the implementation of the Jabber compiler fall into several distinct areas, and as such this section has been divided into several subsections to discuss each area individually. The first among these is a more theoretical concern about the correctness of the compiler, while the remainder are more technical concerns about the underlying code.

=== Correctness

We begin with the most obvious issue with this implementation of Jabber: it is incomplete. To be precise, it lacks
- pattern exhaustiveness analysis;
- infinite type detection;
- cyclic constant definition detection, and;
- several other small semantic checks related to opaque types.

We should obviously understand this to be a failure to meet the articulated objectives of Jabber, but not by a substantial margin; the brevity of this list is evidence that the compiler is not far removed from correctly implementing Jabber, and could be made complete with a short period of additional work.

=== Architecture

A less obvious problem with the compiler relates to its fundamental architecture, which requires the driver to manually chain compiler stages together and manage any intermediary state. This #short("api") is brittle, prone to breaking whenever any individual stage is changed. There is also a reliance on some pervasive global state, particularly in the `unique` module; a single global mutable variable is used to implement `unique::Uid::fresh`, which prevents any kind of meaningful parallelisation.

It can be broadly said that this architecture is arbitrary and inconsistent, with individual segments of the codebase reflecting their relative ages in their designs. The most coherent elements of the compiler are the `env` and `ast` modules, but even here we can see an evolution in design and code quality over time.

=== Front End <subsection-evaluation-compiler-front-end>

As discussed, the parser front end was implemented in #short("tree-sitter") rather than @rust. While this decision was originally made for efficiency, as it made iteration on the grammar easier and faster, it became more of a burden on later parts of the compiler as time progressed.

Parser generators are powerful tools, but they are known to produce extremely cryptic and unhelpful error messages; the compiler's parser is no different in this regard. It also results in a huge chunk of generated Rust code when processed by `typesitter`, up to some 35,000 lines depending on compiler settings; this slows compile times and detracts from some of the iteration speed benefits of a parser generator.

=== Middle End

The middle end is the largest and most complex of the compiler stages, and as such it suffers the most from architectural inconsistency; in a few particular places it is a tangled mess of stateful functions and implicit invariants.

Much of the complexity here stems from the goal of providing useful error messages, which necessitated several complete rewrites of the `env::typing` and `ast::typing` modules, as well as the introduction of a whole family of types like `Span`, `Loc`, and `Blame` for tracking various relationships between the compiler data and the source files.

=== Back End

As the most recently implemented compiler stage, the back end benefits from the pyrrhic lessons learned in the earlier stages. It is simpler, more modular, and had clear inputs and outputs in its interface from the very beginning.

However, the back end has a fairly _ad hoc_ architecture based around the `Lowerer` type, which inconsistently memoises its methods using manual implementation techniques. This design is inherently prone to mistakes and accidental memory overuse, which were common problems during development.

== Distribution <section-evaluation-distribution>

Jabber's current distribution model is extremely rudimentary, relying on end users having access to several tools—including a full @rust toolchain—and being willing and able to build the compiler on their own hardware. Moreover, they must independently install @racket and its @r6rs language module by themselves before they are able to run any compiled programs. These problems are acceptable in a prototype compiler, but absolutely _must_ be redressed before the compiler can be reasonably considered publically presentable.

= Conclusion <chapter-conclusion>

#quote(attribution: [_Jabberwocky_ by Lewis Carroll, 1871])[
  'Twas brillig, and the slithy toves\
  Did gyre and gimble in the wabe:\
  All mimsy were the borogoves\
  And the mome raths outgrabe.
]

The preamble of @chapter-impl presented a view of compilers as programs composed of a series of stages, each consuming the output of its immediate predecessor. And to be sure, this is the conventional perspective on compiler architecture; the chapters of the canonical Dragon Book #footnote[_Compilers: Principles, Techniques, and Tools_ by Aho, Lam, Sethi, and Ullman @the-dragon-book.] are sequenced to match this serial structure.

But a different perspective is obtained by examining the different kinds of data as they are consumed and produced throughout the compiler. Compilers begin with linear streams of bytes, and then tokens, and then they step up in complexity by dealing with syntax trees. As they move from the front end to the middle end, the individual syntax trees are combined into an assembly of graphs and tables, with relatively little unambiguous structure. Little by little, the middle end massages these graphs into more tractable forms, spitting out warnings and errors as it goes. By the time we reach the _end_ of the middle end, there is a semblance of coherent structure, and a variety of systemic invariants have been established; the tangled mess of raw data has been disassociated into a database of information about the source code. At last, the back end walks back down this hierarchy of complexity; graphs become #short("dag")s, which become trees, which are finally returned to linear streams of bytes.

So the work of a compiler is normally distributed, both in development and at runtime. At the beginning and at the end, it operates on well-structured data, and can often rely on strong invariants about these datatypes; developing these components is a relatively straightforward, pleasant process. By contrast, the middle end constitutes the majority of the interesting and difficult work; it is the place where most problems occur, but also where a language's unique identity is established and implemented. At the extremes, all other pieces of a compiler can be seen simply as scaffolding beneath this central element.

Jabber began as a few fragments of code in a #short("markdown") file that bore almost no resemblance to the language implemented by the compiler, and whose semantics were waved away as a distant future concern. When it came time to build the compiler, those semantics were still vague; it was only in grappling with the complexity of the middle end that they crystallised in their current form.

However you might wish to measure it, most of the effort in this project was directed towards the compiler's middle end. Some early designs were removed entirely when it became clear that the implementation complexity would be too great; in all cases the concern was the implied middle end component.

But very few things have been as satisfying as seeing the very first program compile and run successfully, and to see the string `hello, world!` appear in a terminal.

== Summary <section-conclusion-summary>

This work has been squarely focused on the development of a single novel language, but it has been a highly variable, fractal subject. In @chapter-design we discussed the design of Jabber in terms of its syntax and semantics, tracing the influences of peer languages and their design philosophies. The result was a practical—if informal—description of a language, which could then be used as a lodestar for later work.

In @chapter-formal-types, we gave a formal account of Jabber's type system, emphasising the underlying algebraic structure and making rigorous the notions of uninhabited and singleton types, as well as of isomorphisms of types. We proved some simple theorems of these formal types, showing that particular manipulations of types can be safely performed without altering their meanings; it is precisely these results that the compiler relies upon when it performs the shape analysis described in @subsection-impl-codegen-shape-analysis.

Then in @chapter-impl we describe how we moved from theory to practice by actually implementing Jabber with a compiler, the result of which was a codebase of some 17,000 lines of @rust, @racket, @scheme, @javascript, and of course, Jabber. The first commits to this project date back almost 10 months to early June 2024, and several hundred commits later we have arrived at a functional compiler that can build and run most Jabber programs. It incorporates theoretical elements in its name resolution and type checking stages, as well as pragmatic concerns around memory allocation and overall performance. It is cross-platform, builds reproducibly, and can be readily distributed by way of @cargo and the @rust toolchain.

Lastly, we critically evaluated the results of the project in @chapter-evaluation, with a focus on identifying problematic areas that could benefit from further attention. Particular attention was paid to the compiler's codebase, where architectural consistency, correctness, and maintainability were identified as areas of weakness. Concerns about the design of Jabber itself were also raised, particularly with respect to some elements of its grammar.

== Future Work <section-conclusion-future-work>

Of course, Jabber is far from complete, and nowhere near the standards expected of mainstream languages. At best, it is a _minimum viable product,_ and will require substantial additional work before it could even be considered a viable, "real" language. Consider that even research languages like @idris2, @koka, and @flix have language servers and formatters available through user-friendly @vscode plugins, whereas Jabber has precisely none of these things. #footnote[Jabber does have a syntax highlighter however! The parser defined in `/tree-sitter-jabber` also includes a query file that defines semantic roles for language elements, and editors like @neovim and @helix can use it for basic syntax highlighting of `.jbr` files.]

This section of the report can be considered a continuation of the critical remarks in @chapter-evaluation, where problems were identified without corresponding solutions—hence we will discuss such solutions here. The following subsections are roughly divided such that each matches a major topics in this document, with an additional final two subsections on tooling (@subsection-conclusion-future-work-tooling) and distribution (@subsection-conclusion-future-work-distribution) to cover topics that have been otherwise absent.

=== Grammar

As discussed in @section-evaluation-syntax, there are several language elements and rules that fit awkwardly alongside the rest of the language; in particular these are the if-else expressions and the implicit function block body rule. Jabber's grammar will need to be revised to remove these.

This would also be an opportunity to add new language elements to the grammar, which would be necessary for some of the other potential future work. For an example of a purely grammatical addition, it would be useful to add raw string and byte string literals in the style of @rust @the-rust-reference[§2.6].

=== Type System

Jabber's type system was designed around simplicity, but its simplicity must be balanced around the holistic simplicity of the entire language. If it makes writing certain kinds of programs more complicated, can we really say that the type system is simple? We consider here some potential type system extensions that would simplify the overall language, even if they might increase the complexity of the type system in isolation.

A common extension for functional type systems is some kind of _implicit programming_, a language feature that allows the compiler to supply implicit arguments to functions when they are invoked. @haskell's type classes are a prominent example, as are @rust's traits; @scala's implicits offer an alternative formulation that trades away guarantees of global coherence for more flexible usage. Relevant here is the proposal for @ocaml to include _modular implicits_ @ocaml-modular-implicits, which modify @scala's implicits to better fit within @ocaml. Jabber could lean in this direction to implement a similar system of modular implicits, drawing from the work on #smallcaps[Cochis] @cochis-paper to make stronger guarantees around coherence while retaining some of flexibility afforded by implicits as compared to global type classes.

Other common extensions include variants of _row polymorphism_ @abstracting-extensible-data-types and _generalised algebraic data types_ (#short("gadt")s) @the-essence-of-gadts, which can help to model some of the patterns found in other programming paradigms, particularly object-oriented patterns.

=== Formalisation

The formalisation work of @chapter-formal-types was solely focused on the type system, with the stated goal of providing a rigorous model with which to analyse the algebraic structure of types in Jabber. But this would seem to lead us towards two different questions: what about the rest of the type system, and what about the rest of the language?

First, the other elements of the type system. Although the $"Type"$ model describes the underlying algebraic structure of types accurately, it largely skips details related to the behaviour of names and variables, instead collapsing them into a black box of symbols. Doing this makes the overall analysis simpler, but the model loses some descriptive power as a result: it has nothing to say about the meaning of @polytype:pl as compared to @monotype:pl, and cannot properly distinguish between variables bound by a quantifier and names left unbound in the global environment. More work is required to build a stronger model for the type system that can provide better answers in these cases.

The second question is about building a rigorous semantic model for the entire language, capable of proving useful properties about Jabber as a complete object. Other languages do have models of this kind, most famously @ml @the-definition-of-standard-ml and to a lesser extent @scheme @r6rs-report[Appendix A], @r7rs-small-report[§7.2]. But it is a testament to the complexity of this task that so few languages have proper, rigorous models, and as such it is probably infeasible and unnecessary to build such a model for Jabber.

=== Implementation

There are far too many necessary changes to the compiler implementation to be described here completely, but we can consider a few of the most important examples.

As mentioned in @subsection-evaluation-compiler-front-end, it has become apparent that using @tree-sitter as a parser generator for the compiler would be a bad choice in the longer term, and hence it needs to be replaced with a stabler alternative. This could either be a handwritten parser using the `winnow` crate, or possibly a @rust\-native parser generator like @lalrpop. This is also an opportunity to improve the error messages produced by the parser, since @tree-sitter's error messages are exceptionally poor in comparison to these alternatives.

The middle end is need of a general architectural overhaul, with a particular focus on standardising the techniques used for storing and passing around core compiler data structures. One thread that would be interesting to pursue in this regard is @rustc's query-based architecture @rustc-dev-guide[§31], which can be seen as an inversion of the conventional feed-forward compiler design. This design pattern is also used by @rust-analyzer, which has extracted it out into the `salsa` crate for general use in other projects. Beyond simply standardising the overall architecture of the middle end, this design would enable some powerful incremental computation and caching techniques to accelerate compilation speed and amortise it over multiple invocations.

Finally, the compiler's error tracking and printing system is extremely rudimentary, and would benefit from dedicated work. This means both improving the accuracy and specificity of error messages, as well as the quality of the resulting output. Both the `miette` and `ariadne` crates are established as prominent tools for producing error messages in @rust compilers, though more preliminary work would be necessary to establish a basic error handling architecture before a choice between the two could be reasonably made.

=== Tooling <subsection-conclusion-future-work-tooling>

This report has largely considered language design and implementation in the abstract, without special attention to the expectations of potential users; it has been an academic topic rather than a public product. If Jabber were to become a public, user-focused language, it would be unthinkable to not also provide some standard tooling alongside it.

The most important modern language tool is a _language server_, a program that implements the _language server protocol_ (#short("lsp")) @language-server-protocol-spec. Language servers provide the framework for all the niceties of code editing, like automatic renaming, semantic navigation, and standardised editor integrations. Even small, new languages like @gleam and @elm provide language servers, with @gleam in particular making its language server available nearly two years before it reached verion 1.0 @gleam-lsp-announcement-post.

Other common tools include formatters, documentation generators, and syntax highlighters, though these are often also built into the language server to benefit from additional semantic information that a simple parser cannot provide alone.

=== Distribution <subsection-conclusion-future-work-distribution>

To use a language, you first need to have access to that language! The final hurdle in language development is getting it to its users, a topic generally referred to as _distribution_. Whether a language is easy or hard to install can have a substantial impact on its success.
#footnote[Take @chez as an example; part of the reason this project doesn't use it is that it's much harder to install on non-Unix platforms like Windows, whereas @racket is relatively straightforward to install almost anywhere.]

Further work is required to determine how Jabber should be distributed. Which operating systems should it support? Should it use the system package manager or a custom package manager in the pattern of #gls("cargo", display: `cargo`) or @elan? Where will the the standard libraries be stored in the file system? These questions must be answered before any practical implementation work can begin.

// END MATTER

#set heading(numbering: none)
#show heading.where(level: 1): it => {
  pagebreak(weak: true)
  set text(size: 24pt)
  [#it #v(10pt)]
}

= References

#set bibliography(title: none)
#bibliography("references.bib")

= Glossary
#print-glossary(entry-list)


= Appendices
#counter(heading).update(1)
#set heading(supplement: "Appendix")
#show heading.where(level: 2): set heading(numbering: (
  _,
  second,
  ..,
) => [A#second])

== Formal Grammar <appendix-formal-grammar>
The following grammar is given in Extended Backus-Naur Form (EBNF). Because Jabber is not whitespace sensitive, rules describing whitespace are provided at the bottom of the grammar and are _implied_ to appear optionally between any two consecutive rules. The binary and infix operator expression rules are partially ambiguous as presented; refer to @appendix-operator-tables for a more precise description of the operators in Jabber.

#let appendix-grammar-figure-spacing = 1em

=== Lexical Syntax

The grammar rules in this section are distinguished from the rest of the language in that they do not admit arbitrary whitespace between adjacent rules.

#align(center)[
  #figure(
    caption: [The comment and whitespace rules.],
    ```ebnf
    comment = line comment
            | doc comment
            | module comment
            ;

    line comment    = ? regex: "//[^\n]*"  ? ;
    doc comment     = ? regex: "//![^\n]*" ? ;
    module comment  = ? regex: "///[^\n]*" ? ;

    whitespace = ? a nonempty string of Pattern_White_Space unicode characters ? ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The name, path, and identifier rules.],
    ```ebnf
    name = path | identifier ;

    path = name, ".", identifier ;

    identifier = ? regex: "(_+[a-zA-Z0-9]|[a-zA-Z])[_a-zA-Z0-9]*" ? ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The non-numeric literal rules.],
    ```ebnf
    unit literal = "(", ")" ;
    true literal = "true" ;
    false literal = "false" ;
    char literal = ? regex: "'(\\'|.|\\u\{[0-9a-fA-F]+\}|\\x\d+|\\.)'" ? ;
    string literal = ? regex: '"(\\"|[^"\r])*"' ? ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The prefix and binary operator rules.],
    ```ebnf
    prefix operator  = "!" | "*" | "-" | "-." ;
    binary operator  = "^"  | "^."
                     | "<|" | "|>"
                     | "==" | "!="
                     | ">"  | "<"  | ">="  | "<="
                     | ">." | "<." | ">=." | "<=."
                     | "+"  | "-"
                     | "+." | "-."
                     | "*"  | "/"
                     | "*." | "/."
                     | "%"
                     | "::" | "++"
                     | "&&" | "||"
                     | ":=" | "<-"
                     ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The numeric literal rules.],
    ```ebnf
    number literal = float literal
                   | integer literal
                   ;

    float literal = dec literal,  ".", dec literal
                  | dec literal, [".", dec literal], exponent
                  ;

    exponent = ("e" | "E"), ["+" | "-"], dec literal ;

    integer literal = bin literal
                    | oct literal
                    | dec literal
                    | hex literal
                    ;

    bin literal = bin prefix, {bin digit | "_"}, bin digit, {bin digit | "_"} ;
    oct literal = oct prefix, {oct digit | "_"}, oct digit, {oct digit | "_"} ;
    dec literal =                                dec digit, {dec digit | "_"} ;
    hex literal = hex prefix, {hex digit | "_"}, hex digit, {hex digit | "_"} ;

    bin prefix = "0b" ;
    oct prefix = "0o" ;
    hex prefix = "0", ("x" | "X") ;

    bin digit = "0" | "1" ;
    oct digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" ;
    dec digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9" ;
    hex digit = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
              | "a" | "b" | "c" | "d" | "e" | "f"
              | "A" | "B" | "C" | "D" | "E" | "F"
              ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#pagebreak(weak: true)
=== Declarations

#align(center)[
  #figure(
    caption: [The starting symbol, attribute, and top-level declaration rules.],
    ```ebnf
    START = {declaration} ;

    declaration = {attributes}, [visibility], declaration body ;
    visibility = "pub" ;

    attributes = { attribute } ;
    attribute = "@", name, ["(", {attribute argument}, ")"] ;
    attribute argument = name | literal expr ;

    declaration body = mod decl              (* modules *)
                     | use decl              (* imports *)
                     | type alias decl       (* type aliases *)
                     | type decl             (* custom types *)
                     | extern type decl      (* foreign types *)
                     | fn decl               (* functions *)
                     | extern fn decl        (* foreign functions *)
                     | const decl            (* constants *)
                     ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The module and use declaration rules.],
    ```ebnf
    mod decl = "mod", identifier ;

    use decl = "use", use item ;

    use item = name
             | glob item
             | alias item
             | tree item
             ;

    alias item = name, "as", ident ;
    tree item  = [name, "."], "{", [use item, {",", use item}, [","]], "}" ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The type, external type, and type alias declaration rules.],
    ```ebnf
    type decl        =           "type", type name, "=", type constructors ;
    extern type decl = "extern", "type", type name ;
    type alias decl  = "type",  "alias", type name, "=", type ;

    type name = ident, [generic parameters] ;
    generic parameters = "[", ident, {",", ident}, [","], "]" ;

    type constructors = {type constructor} ;
    type constructor  = ident, [record payload | tuple payload] ;

    record payload = "{" record field, {",", record field}, [","], "}" ;
    tuple payload  = "("         type, {",",         type}, [","], ")" ;

    record field = ["mutable"], ident, ":", type ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The function, external function, and constant declaration rules.],
    ```ebnf
    fn decl        =           "fn", ident, parameters, ["->", type], fn body;
    extern fn decl = "extern", "fn", ident, parameters, ["->", type];

    parameters = "(", [parameter, {"," parameter}, [","]], ")" ;
    parameter  = pattern, [":", type] ;

    fn body = ("=", expr) | block ;

    const decl  = "const", ident, ":", type, "=", expr ;
    ```,
  )
]

=== Expressions

#align(center)[
  #figure(
    caption: [The top-level expression and literal expression rules.],
    ```ebnf
    expr = name                     (* items *)
         | literal expr             (* literals *)
         | list expr                (* lists *)
         | tuple expr               (* tuples *)
         | record expr              (* record literals *)
         | field expr               (* projections *)
         | lambda expr              (* function literals *)
         | call expr                (* function calls *)
         | prefix expr              (* prefix operators *)
         | binary expr              (* infix operators *)
         | match expr               (* pattern matches *)
         | if expr                  (* boolean conditionals *)
         | parenthesized expr       (* parentheses *)
         | block                    (* block-scoped expressions *)
         ;

    literal expr = unit literal
                 | true literal
                 | false literal
                 | character literal
                 | string literal
                 | number literal
                 ;
    ```,
  )
]

#v(appendix-grammar-figure-spacing)

#align(center)[
  #figure(
    caption: [The specific expression rules.],
    ```ebnf
    list expr  = "[", [expr, {",", expr}, [","]], "]" ;
    tuple expr = "(",  expr, {",", expr}, [","],  ")" ;

    record expr = name,
                  "{", record expr field, {",", record expr field},
                 [",", record expr base],
                 [","], "}" ;

    record expr field = ident, [":", expr] ;
    record expr base = "..", expr ;

    field expr = expr, ".", ident ;

    lambda expr = (ident | parameters), "->", expr ;

    prefix expr  = prefix operator, expr ;
    binary expr  = expr, binary operator, expr ;

    call expr = expr, "(", [expr, {",", expr}, [","]], ")" ;

    match expr = "match", expr, match arms ;
    match arms = "{", [match arm, {",", match arm}, [","]], "}" ;
    match arm = pattern, ["if", expr], "=>" expr ;

    if expr = "if", expr, block, [else clause] ;
    else clause = "else" (if expr | block) ;

    block = "{", {stmt}, [expr], "}" ;
    stmt = ";" | expr stmt | let stmt ;
    expr stmt = expr, ";" ;
    let stmt = "let", pattern, [":", type], "=", expr, ";" ;

    parenthesized expr = "(", expr, ")" ;
    ```,
  )
]

#pagebreak(weak: true)
=== Patterns

#align(center)[
  #figure(
    caption: [The top-level and specific pattern rules.],
    ```ebnf
    pattern = "_"
            | name
            | literal expr
            | tuple pattern
            | list pattern
            | cons pattern
            | tuple constructor pattern
            | record constructor pattern
            | parenthesized pattern
            ;

    tuple pattern = "(",  pattern, {",", pattern}, [","],  ")" ;
    list pattern  = "[", [pattern, {",", pattern}, [","]], "]" ;

    cons pattern = pattern, "::", pattern ;

    tuple constructor pattern = name, "(", pattern, {",", pattern}, [","], ")" ;

    record constructor pattern =
                    name,
                    "{", record pattern field, {",", record pattern field},
                   [",", rest pattern],
                   [","], "}" ;

    record pattern field = ident, [":", type] ;
    rest pattern = ".." ;

    parenthesized pattern = "(", pattern, ")" ;
    ```,
  )
]

#pagebreak(weak: true)
=== Types

#align(center)[
  #figure(
    caption: [The top-level and specific type rules.],
    ```ebnf
    type = "_"
         | name
         | primitive type
         | unit type
         | tuple type
         | generic type
         | function type
         | parenthesized type
         ;

    primitive type = "!"
                   | "bool"
                   | "char"
                   | "string"
                   | "int"
                   | "float"
                   ;

    unit type = "(", ")" ;

    tuple type = "(", type, ",", type, {",", type}, [","], ")" ;

    generic type = name, "[", type, {",", type}, [","], "]" ;

    function type = type, "->", type ;

    parenthesized type = "(", type, ")" ;
    ```,
  )
]

#show heading.where(level: 2): it => {
  pagebreak(weak: true)
  it
}

#show heading.where(level: 3): set heading(outlined: false)
#show heading.where(level: 4): set heading(outlined: false)

== Dependencies <appendix-dependencies>

#figure(
  caption: [The dependencies used throughout the entire project.],
  table(
    columns: (2fr, 7fr),
    inset: (x, y) => if y != 0 and x != 0 {
      (x: 40pt, y: 6pt)
    } else {
      6pt
    },
    align: (x, y) => if y != 0 and x != 0 {
      left
    } else {
      center
    },
    [*Name*], [*Description*],
    table.cell(
      colspan: 2,
      [*Rust Crates* #footnote[Unless otherwise stated, all Rust crates are available on #link("crates.io") under their listed names.]],
    ),
    [`clap`], [A standard tool for building CLIs in Rust.],
    [`ena`], [A generic union-find implementation used by `rustc`.],
    [`petgraph`], [A collection of graph data structures and algorithms.],
    [`pretty`], [A collection of Wadler-style pretty printer combinators.],
    [`recursion`], [Abstractions for mimicking recursion schemes in Rust.],
    [`semver`], [An implementation of the Semver standard.],
    [`serde`], [Generated serialisers and deserialisers.],
    [`string-interner`], [A simple string interner implementation.],
    [`thiserror`], [Macros for creating error types.],
    [`toml`], [A parser for the #short("toml") file format.],
    [`type-sitter`], [A code generator for type-safe #short("tree-sitter") #short("rust") bindings.],
    [`which`], [Emulates the Unix `which` command.],
    [`winnow`], [A parser combinator library],
    table.cell(colspan: 2, [*Tools*]),
    [Rust], [The Rust programming language.],
    [Racket], [The Racket programming language.],
    [Tree-Sitter], [A parser-generator framework.]
  ),
)

== Operators <appendix-operator-tables>

#let prec = (
  lambda: 0,
  update: 1,
  lazy_or: 2,
  lazy_and: 3,
  pipe_right: 4,
  pipe_left: 5,
  cmp: 6,
  cons: 7,
  add: 8,
  mul: 9,
  pow: 10,
)

#figure(
  caption: [Jabber's binary operators],
  table(
    columns: (auto, auto, auto, auto, 1fr),
    rows: (20pt,) * 27,
    [*Op.*], [*Prec.*], [*Assoc.*], [*Definition*], [*Type*],

    // pow (^ and ^.)
    [`^`], [#prec.pow], [Right], [`core.int.pow`], [`(int, int) -> int`],
    [`^.`], [#prec.pow], [Right], [`core.float.pow`], [`(float, float) -> float`],

    // mul-precedence (*, *., /, /., %)
    [`%`], [#prec.mul], [Left], [`core.int.mod`], [`(int, int) -> int`],
    [`*`], [#prec.mul], [Left], [`core.int.mul`], [`(int, int) -> int`],
    [`/`], [#prec.mul], [Left], [`core.int.div`], [`(int, int) -> int`],
    [`*.`], [#prec.mul], [Left], [`core.float.mul`], [`(float, float) -> float`],
    [`/.`], [#prec.mul], [Left], [`core.float.div`], [`(float, float) -> float`],

    // add-precedence (+, +., -, -., )
    [`+`], [#prec.add], [Left], [`core.int.add`], [`(int, int) -> int`],
    [`-`], [#prec.add], [Left], [`core.int.sub`], [`(int, int) -> int`],
    [`+.`], [#prec.add], [Left], [`core.float.add`], [`(float, float) -> float`],
    [`-.`], [#prec.add], [Left], [`core.float.sub`], [`(float, float) -> float`],

    // list operators (:: and ++)
    [`::`], [#prec.cons], [Right], [`core.list.List.Cons`], [`(A, List[A]) -> List[A]`],
    [`++`], [#prec.cons], [Right], [`core.list.concat`], [`(List[A], List[A]) -> List[A]`],

    // cmp (==, !=, >, >., <, <., >=, >=., <=, <=.)
    [`==`], [#prec.cmp], [Left], [`core.cmp.eq`], [`(A, A) -> bool`],
    [`!=`], [#prec.cmp], [Left], [`core.cmp.neq`], [`(A, A) -> bool`],
    [`>`], [#prec.cmp], [Left], [`core.int.gt`], [`(int, int) -> bool`],
    [`<`], [#prec.cmp], [Left], [`core.int.lt`], [`(int, int) -> bool`],
    [`>=`], [#prec.cmp], [Left], [`core.int.geq`], [`(int, int) -> bool`],
    [`<=`], [#prec.cmp], [Left], [`core.int.leq`], [`(int, int) -> bool`],
    [`>.`], [#prec.cmp], [Left], [`core.float.gt`], [`(float, float) -> bool`],
    [`<.`], [#prec.cmp], [Left], [`core.float.lt`], [`(float, float) -> bool`],
    [`>=.`], [#prec.cmp], [Left], [`core.float.geq`], [`(float, float) -> bool`],
    [`<=.`], [#prec.cmp], [Left], [`core.float.leq`], [`(float, float) -> bool`],

    // pipe left (<|)
    [`<|`], [#prec.pipe_left], [Right], [`core.fun.pipe_left`], [`(A -> B, A) -> B`],

    // pipe right (|>)
    [`|>`], [#prec.pipe_right], [Left], [`core.fun.pipe_right`], [`(A, A -> B) -> B`],

    // update operator (walrus, :=)
    [`:=`], [#prec.update], [Right], [`core.ref.update`], [`(Ref[T], T) -> ()`],

  ),
) <figure-binary-operator-table>

#let prefix_operator_table = figure(
  caption: [Jabber's prefix operators],
  table(
    columns: (auto, auto, auto),
    rows: (20pt,) * 5,
    [*Op.*], [*Definition*], [*Type*],
    [`!`], [`core.bool.not`], [`bool -> bool`],
    [`*`], [`core.ref.deref`], [`Ref[T] -> T`],
    [`-`], [`core.int.neg`], [`int -> int`],
    [`-.`], [`core.float.neg`], [`float -> float`],
  ),
)

#let primitive_operator_table = figure(
  caption: [Jabber's primitive binary operators],
  table(
    columns: (auto, auto, auto, auto),
    rows: (20pt,) * 5,
    [*Op.*], [*Prec.*], [*Assoc.*], [*Meaning*],

    // lazy and (&&)
    [`&&`], [#prec.lazy_and], [Right], [Lazy AND],

    // lazy or (||)
    [`||`], [#prec.lazy_or], [Right], [Lazy OR],

    // record field mutation operator
    [`<-`], [#prec.update], [Right], [Mutate],

    // lambdas
    [`->`], [#prec.lambda], [Right], [Lambda],
  ),
)

#grid(
  columns: (1fr, 1fr),
  [#prefix_operator_table <figure-prefix-operator-table>],
  [#primitive_operator_table <figure-primitive-operator-table>],
)


== Example Jabber Programs

==== Hello World
```jabber
fn main() = println("hello, world!")
```
#line(length: 100%)

==== Fibonacci Numbers
```jabber
fn fib(n: int) -> int = match n {
    0 => 1,
    1 => 1,
    x =>  if x > 0 { fib(x - 1) + fib(x - 2) } else { panic() },
}
```
#line(length: 100%)

==== Binary Trees

```jabber
type BTree[T] =
  | Leaf(T)
  | Node { lhs: BTree[T], value: T, rhs: BTree[T] }

fn invert(tree) = match tree {
    BTree.Leaf(x) => BTree.Leaf(x),
    BTree.Node { lhs, value, rhs }
      => BTree.Node { lhs: rhs, value, rhs: lhs },
}
```
#line(length: 100%)

==== Lists
```jabber
// [] and :: are syntax sugar for Nil and Cons
type List[T] = Nil | Cons(T, List[T])

fn length(xs) -> int = match xs {
  []          => 0,
  (_ :: tail) => 1 + length(tail),
}

fn map(xs: List[A], f: A -> B) = match xs {
  []        => [],
  (x :: xs) => f(x) :: map(xs, f),
}
```
#line(length: 100%)

==== Reference Cells

```jabber
type Ref[T] = Ref { mutable contents : T }

fn ref(contents: T) -> Ref[T] = Ref { contents }

fn deref(Ref { contents }: Ref[T]) -> T = contents

fn update(ref: Ref[T], new: T) {
    ref.contents <- new;
}
```

== Installation and Usage <appendix-installation-and-usage>

The following tools are prerequisites for building and running the compiler:

+ A recent version of the @rust toolchain, at least version 1.85.1.
+ #short("tree-sitter"), which can be installed with the @rust toolchain: `cargo install tree-sitter-cli`.
+ A @c compiler, for example MSVC or Clang.
+ A @racket installation with the `r6rs` language package, for which there are two options:
  - Install the larger `racket` package for your system, or;
  - Install the `racket-minimal` package and run `raco pkg install r6rs`.

With these prerequisites installed, you can build, install, and use the compiler from the command line (@figure-installation-script). If you don't want to install the compiler locally, you can still run it by replacing any occurrence of `jabber` with `cargo run --` in the `/compiler` subdirectory.

#align(center)[
  #figure(
    caption: [A shell script for installing and using the compiler.],
    ```sh
    # generate the tree-sitter parser
    cd tree-sitter-jabber
    tree-sitter generate
    # build and install the compiler
    cd ../compiler
    cargo install --path .
    # run the /tests/hello_world program
    jabber -l ../libs run -s ../support -i ../tests/hello_world
    ```,
  ) <figure-installation-script>
]

With the `just` tool installed, #footnote[Also available via the @rust toolchain with `cargo install just`.] you can also run Jabber programs by invoking ```sh just run PROGRAM``` anywhere in the project directory tree; for example `just run tests/hello_world` produces the same output as the shell script in @figure-installation-script. You can also run the automated test suite by invoking `just test`, though do be aware that the @tree-sitter tests may be flaky on Windows hosts.

