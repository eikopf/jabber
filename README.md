# Jabber

> 'Twas brillig, and the slithy toves  
> Did gyre and gimble in the wabe;  
> All mimsy were the borogoves,  
> And the mome raths outgrabe.

## Requirements

To use this project, you will need:
1. A recent Rust toolchain, at least 1.85.1.
2. A local C compiler.
3. A Racket installation with the R6RS language package.

## Usage
For any of the following commands, `jabber` can be exchanged with `cargo run --` if you're in the project directory.

- `jabber`, `jabber help`, and `jabber --help` will display some usage instructions in the terminal.
- `jabber -l <LIBS_ROOT> compile -i <INPUT_ROOT> -o <OUTPUT_ROOT>` will compile the package at `<INPUT_ROOT>` against the libraries in `<LIBS_ROOT>` and place the files in `<OUTPUT_ROOT>`.
- `jabber -l <LIBS_ROOT> run -s <SUPPORT_ROOT> -i <INPUT_ROOT> -o <OUTPUT_ROOT>` will compile as above, but then will also run the package using `racket` with the given `<SUPPORT_ROOT>`.

## Index
- [`compiler`](compiler/) is the root of the Rust crate that implements the Jabber compiler.
- [`libs`](libs/) contains Jabber's standard libraries, of which the most important is [`core`](libs/core/).
- [`spec`](spec/) contains normative (binding) documents describing Jabber, and is intended to be the source of truth for the language;
- [`support`](support/) contains the runtime support library used by the compiled Racket artifacts.
- [`tests`](tests/) contains several Jabber packages to test the compiler against.
- [`tree-sitter-jabber`](tree-sitter-jabber/) is a [Tree-sitter](https://tree-sitter.github.io/tree-sitter/) parser for Jabber, defined in [`grammar.js`](tree-sitter-jabber/grammar.js) --- it also serves as the front-end CST parser for the Jabber compiler.

## Notes
 - The artifacts in [`tree-sitter-jabber/src`](tree-sitter-jabber/src) will change slightly based on the system that runs `tree-sitter generate`. Systems can run `git update-index --assume-unchanged <FILENAME>` to locally ignore changes to these files.
 - Tree-sitter appears to currently have a bug that causes `tree-sitter test` to ignore test tags on Windows.
