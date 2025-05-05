// glossary term definitions

#let entry-list = (
  // ACRONYMS
  (
    key: "abi",
    short: "ABI",
    long: "Application Binary Interface",
  ),
  (
    key: "ast",
    short: "AST",
    long: "Abstract Syntax Tree",
  ),
  (
    key: "adt",
    short: "ADT",
    long: "Algebraic Datatype",
  ),
  (
    key: "api",
    short: "API",
    long: "Application Programming Interface",
  ),
  (
    key: "bnf",
    short: "BNF",
    long: "Backus-Naur Form",
  ),
  (
    key: "cst",
    short: "CST",
    long: "Concrete Syntax Tree",
  ),
  (
    key: "dsl",
    short: "DSL",
    long: "Domain Specific Language",
    //group: "Acronyms",
  ),
  (
    key: "dag",
    short: "DAG",
    long: "Directed Acyclic Graph"
  ),
  (
    key: "ir",
    short: "IR",
    long: "Internal Representation",
  ),
  (
    key: "r6rs",
    short: "R6RS",
    long: "The Revised⁶ Report on the Algorithm Language Scheme",
  ),
  (
    key: "gadt",
    short: "GADT",
    long: "Generalised Algebraic Data Type",
  ),
  (
    key: "lsp",
    short: "LSP",
    long: "Language Server Protocol",
  ),

  // TOOLS
  (
    key: "elan",
    short: [`elan`],
    description: "The standard package manager for Lean",
  ),
  (
    key: "cargo",
    short: "Cargo",
    description: "The standard build tool for the Rust toolchain."
  ),
  (
    key: "tree-sitter",
    short: "Tree-Sitter",
    description: "A language-agnostic parser-generator framework.",
  ),
  (
    key: "markdown",
    short: "Markdown",
    description: "A plain-text markup language.",
  ),
  (
    key: "vscode",
    short: "VSCode",
    description: "A major text editor owned by Microsoft.",
  ),
  (
    key: "neovim",
    short: "NeoVim",
    description: "A modern fork of the text editor Vim.",
  ),
  (
    key: "helix",
    short: "Helix",
    description: "A simple text editor in the mould of Kakoune.",
  ),
  (
    key: "lalrpop",
    short: "LALRPOP",
    description: "A Rust-based parser generator framework.",
  ),
  (
    key: "rustc",
    short: [`rustc`],
    description: "The canonical Rust compiler.",
  ),
  (
    key: "rust-analyzer",
    short: [`rust-analyzer`],
    description: "The standard Rust language server.",
  ),

  // TERMS
  (
    key: "identifier",
    short: "identifier",
    description: "A language element defining allowed non-keyword symbols, found in almost all languages.",
  ),
  (
    key: "monotype",
    short: "monotype",
    description: [A type without universally quantified variables.],
  ),
  (
    key: "polytype",
    short: "polytype",
    description: [A type containing some universally quantified variables, sometimes also called a type scheme.]
  ),
  (
    key: "llvm",
    short: "LLVM",
    description: [A target-independent optimiser and code generator used as the backend for many major language implementations.],
  ),
  (
    key: "system-f",
    short: "System F",
    description: "The polymorphic lambda calculus."
  ),
  (
    key: "unicode",
    short: "Unicode",
    description: [A common set of standards for encoding strings and characters, defined by the Unicode Standard @unicode-standard-16 and controlled by the Unicode Consortium.]
  ),
  (
    key: "unicode-scalar-value",
    short: "Unicode scalar value",
    description: [Any Unicode code point in the ranges 0 to D7FF#sub[16] and E000#sub[16] to 10FFFF#sub[16] (inclusive) @unicode-standard-16[§3.9, D76].]
  ),
  (
    key: "unicode-code-point",
    short: "Unicode code point",
    description: [An integer in the range from 0 to 10FFFF#sub[16] @unicode-standard-16[§3.4, D10].],
  ),
  (
    key: "utf8",
    short: "UTF-8",
    description: [A Unicode encoding that assigns to each Unicode scalar value an unsigned byte sequence between one and four bytes in length @unicode-standard-16[§3.9.3, D92].],
  ),
  (
    key: "union-find",
    short: "union–find",
    description: [A data structure that stores disjoint sets and efficiently computes membership of any of its member sets for a given key.]
  ),

  // LANGUAGES
  (
    key: "algol",
    short: "ALGOL",
    description: "A family of early programming languages from the late 1950s.",
  ),
  (
    key: "fortran",
    short: "FORTRAN",
    description: "An early programming language from the late 1950s.",
  ),
  (
    key: "austral",
    short: "Austral",
    description: "A systems programming language."
  ),
  (
    key: "elm",
    short: "Elm",
    description: "A functional language related to Haskell."
  ),
  (
    key: "flix",
    short: "Flix",
    description: "A functional research language with an algebraic effects system and region-based memory management."
  ),
  (
    key: "idris2",
    short: "Idris2",
    description: "A dependently-typed research language related to Haskell."
  ),
  (
    key: "gleam",
    short: "Gleam",
    description: "An immutable functional language."
  ),
  (
    key: "toml",
    short: "TOML",
    long: "Tom's Obvious Minimal Language",
    description: "A human-readable configuration file format."
  ),
  (
    key: "haskell",
    short: "Haskell",
    description: "A pure functional language."
  ),
  (
    key: "chez",
    short: "Chez Scheme",
    description: "A major Scheme implementation owned by Cisco.",
  ),
  (
    key: "racket",
    short: "Racket",
    description: "A language-oriented descendant of Scheme.",
  ),
  (
    key: "rust",
    short: "Rust",
    description: "A systems programming language.",
  ),
  (
    key: "python",
    short: "Python",
    description: "A scripting language."
  ),
  (
    key: "julia",
    short: "Julia",
    description: "A scientific computing language."
  ),
  (
    key: "koka",
    short: "Koka",
    description: "An algebraic effect research language."
  ),
  (
    key: "c",
    short: "C",
    description: "A pervasive low-level programming language.",
  ),
  (
    key: "cpp",
    short: "C++",
    description: "A low-level object-oriented language derived from C.",
  ),
  (
    key: "go",
    short: "Go",
    description: "A compiled language focused on simplicity."
  ),
  (
    key: "java",
    short: "Java",
    description: "A pervasive garbage-collected language."
  ),
  (
    key: "javascript",
    short: "JavaScript",
    description: "A pervasive scripting language."
  ),
  (
    key: "scala",
    short: "Scala",
    description: "A functional programming language related to Java."
  ),
  (
    key: "scheme",
    short: "Scheme",
    description: "A major family of Lisp dialects."
  ),
  (
    key: "swift",
    short: "Swift",
    description: "A multiparadigm compiled language."
  ),
  (
    key: "lisp",
    short: "Lisp",
    description: "A broad family of programming languages."
  ),
  (
    key: "ocaml",
    short: "Ocaml",
    description: "A functional language descended from ML.",
  ),
  (
    key: "ml",
    short: "ML",
    description: "An early functional language (ca. 1973)."
  ),
  (
    key: "sml",
    short: "Standard ML",
    description: "A dialect of ML notable for having a complete formal specification."
  ),
  (
    key: "typescript",
    short: "TypeScript",
    description: "A structurally-typed superset of JavaScript.",
  ),
  (
    key: "fennel",
    short: "Fennel",
    description: "A Lisp that compiles to Lua.",
  ),
  (
    key: "lua",
    short: "Lua",
    description: "A small embeddable scripting language."
  ),
)
