# Compiler Architecture
The rough outline for the compiler pipeline is as follows:

1. Lexer
2. Parser
3. HIR
4. HIR-T
5. MIR
6. Backend

The [`rustc` development guide](https://rustc-dev-guide.rust-lang.org/about-this-guide.html) is a very accessible resource for discussions of complex compiler design, particularly when considering the FP-derived trait system.

## Core Design Principles
A good compiler should be

- highly parallelisable;
- memory-efficient;
- friendly to external tooling;
- able to provide detailed error messages.

The first two goals are arguably the same as for any other complex system, but the second two have a clear implication: whenever possible, __keep going__. Most errors are localised, and most code is well-formed most of the time. A compiled language in which you can encounter at most a single error message at a time is no more developer-friendly than Python, and hardly worth the effort. 

Languages like Elm, Gleam, and Rust have put in huge amounts of effort to create and maintain friendly error messages, and they are frequently lauded for doing so. At the very least, the compiler's codebase should be written in a way that allows for simple improvements in this direction.

## Lexer
`TODO`

## Parser
`TODO`

## HIR
`TODO` Discuss type-checking and continuation-passing style; refer to Rust's [HIR](https://rustc-dev-guide.rust-lang.org/hir.html).

## HIR-T
`TODO` A type-checked version of the HIR; compare to Rust's [THIR](https://rustc-dev-guide.rust-lang.org/thir.html)

## MIR
`TODO` Based on a control-flow graph and used for optimizations; compare to Rust's [MIR](https://rustc-dev-guide.rust-lang.org/mir/index.html)
