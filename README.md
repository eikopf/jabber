# Jabber

> 'Twas brillig, and the slithy toves  
> Did gyre and gimble in the wabe;  
> All mimsy were the borogoves,  
> And the mome raths outgrabe.  

## Index
- [`notes`](notes/) contains a number of design documents and language grammars, all of which are (at this point) non-binding;
- [`prototypes`](prototypes/) contains several prototype compiler front-ends, variously written in Rust and OCaml;
- [`tree-sitter-jabber`](tree-sitter-jabber/) is a [Tree-sitter](https://tree-sitter.github.io/tree-sitter/) parser for Jabber, defined in [`grammar.js`](tree-sitter-jabber/grammar.js) --- it also serves as the front-end CST parser for the Jabber compiler.
