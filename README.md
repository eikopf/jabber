# Jabber

> 'Twas brillig, and the slithy toves  
> Did gyre and gimble in the wabe;  
> All mimsy were the borogoves,  
> And the mome raths outgrabe.  

## Index
- [`notes`](notes/) contains a number of design documents and language grammars, all of which are (at this point) non-binding;
- [`spec`](spec/) contains normative (binding) documents describing Jabber, and is intended to be the source of truth for the language;
- [`tree-sitter-jabber`](tree-sitter-jabber/) is a [Tree-sitter](https://tree-sitter.github.io/tree-sitter/) parser for Jabber, defined in [`grammar.js`](tree-sitter-jabber/grammar.js) --- it also serves as the front-end CST parser for the Jabber compiler.

## Notes
 - The artifacts in [`tree-sitter-jabber/src`](tree-sitter-jabber/src) will change slightly based on the system that runs `tree-sitter generate`. Systems can run `git update-index --assume-unchanged <FILENAME>` to locally ignore changes to these files.
 - Tree-sitter appears to currently have a bug that causes `tree-sitter test` to ignore test tags on Windows.
