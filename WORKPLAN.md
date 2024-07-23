# Final Year Project Work Plan

## Stage 0 --- Research
This stage will likely be the shortest, since I can rely on my own prior knowledge. Still, it's important to get this right: the design stage will probably rely heavily on gesturing towards the aggregated research.

For both language design and compiler implementation, I expect research to largely center around prior art and received wisdom; much of the literature dates to the '70s and '80s, and syntactic language design in particular is seen to be a matter of opinion.

I'm hopeful that I can pull from the literature around Idris (i.e. largely the work of Edwin Brady), as well as some of the literature discussing Julia and Rust; this probably implies a focus on type theory for the project as a whole.

## Stage 1 --- Design

### Stage 1.1 --- Language Design
The design of a language can be split into its syntax and its semantics. The syntax of the language can be explicitly given in the form of an EBNF grammar, while the semantic model will likely require defining and describing a core language.

I expect the writing of the grammar to be relatively simple, given a concrete choice of language family and immediate relatives.

Core languages are very common in the FP domain; they are IRs in all but name. The core language will likely be constructed during the CST to AST conversion phase of the compiler, at which point it can be used for type-checking and other kinds of static analysis.

My immediate references here are Idris's core language(s) and Rust's MIR, but I'm also interested in the (less formal) ongoing work on the Polaris and Austral languages.

### Stage 1.2 --- Compiler Design

This stage is a lot less certain, but also does not need to be locked down in the way that the language design necessitates. At this point, I expect the compiler to consist of the following phases:

1. Parsing
1. Name resolution
1. Desugaring
1. Lowering
1. Type checking
1. Monomorphization
1. Codegen
1. Rendering

In doing so, I also expect to use the following general IRs:

1. A concrete syntax tree (CST)
    - Generated during the parsing phase
1. An abstract syntax tree (AST)
    - Generated during the name resolution and desugaring phases
1. A core language
    - Generated during the lowering phase
    - Used in the type-checking and monomorphization phases
1. An R6RS-compatible Scheme IR
    - Generated during the codegen phase
    - Used in the rendering phase

There are a few obvious omissions here that need to be pinned down:

1. How are types represented at runtime?
1. What happens to the standard library? Does it get a special compilation mode?
1. What's the FFI story (both for Scheme and C)?
1. What does the compiler do with the resulting `.scm` files?
1. Does the compiler expect a particular directory structure for packages?

## Stage 2 --- Implementation

Compilers are inherently lumbering projects, so I expect to follow a waterfall(ish) implementation strategy: phase by phase and IR by IR, until the compiler achieves an MVP state. There's little to say at this stage, and a clearer plan will probably emerge once the design stage solidifies.

There are also some auxiliary tasks relating to the compiler:

1. Writing a standard library
1. Writing a prelude
1. Implementing backend features to process the Scheme build artifacts

In addition, the following "stretch goals" are important but non-essential:

1. Converting the grammar into a Tree-sitter grammar to enable syntax highlighting
1. Writing a language server

## Stage 3 --- Evaluation
`TODO`

## Stage 4 --- The Report
`TODO`
