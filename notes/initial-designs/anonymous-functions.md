# Anonymous Functions
## Prior Art

There are a wide variety of syntaxes for anonymous functions, and they often indicate more about the design of the language itself than any other feature. Python and MATLAB, as per usual, are outliers, but most languages fall into these categories:

1. Ruby-derived `|x|`, e.g. Rust;
2. Haskell-derived `\x`, e.g. Idris, Elm, and Kotlin's lambda literals;
3. Imperative Haskell-ish `(x) -> ...`, e.g. Julia and Java;
4. Keyword-constructs like `fn` or `fun`, e.g. Gleam, F#, and Kotlin (also most Lisps).

```
# elm
\x y z -> <expr>

# f#
fun x y z -> <expr>

# gleam
fn(x, y, z) { <expr> }

# haskell
\x y z -> <expr>

# idris
\x y z => <expr>

# java
(x, y, z) -> <expr>

# julia
(x, y, z) -> <expr>

# kotlin
{ x, y, z -> <expr> } or fun(x, y, z) { expr }

# matlab
@(x, y, z) <expr>

# ocaml
fun x y z -> <expr>

# python
lambda x, y, z: <expr>

# rust
|x, y, z| <expr>

# scala
(x, y, z) => <expr>
```

## Type Annotations
It's also worth briefly dipping into type annotations in the statically typed languages.

1. Idris and OCaml use `(x : T)` for explicit typing judgements, and this syntax is used more widely throughout both languages;
2. Gleam and Rust both allow `: T` to appear after variables, so you get forms like `|a: A, b: B|` and `fun(a: A, b: B)`. Again, this syntax matches the typing judgement syntax used throughout both languages;
3. Haskell has no way to write typing judgements on locally-scoped variables (excluding compiler extensions), and infers all types from function type annotations in the global scope.


## "Purity" & Verbosity
Anonymous functions often use novel syntax for parameters, but they otherwise remain very close to the rest of the language. The purest form of this is in languages where the function keyword is also used to introduce parameters. From a lofty perspective of design idealism, this makes perfect sense: an anonymous function is literally just a function with the name omitted!. 

But of course, this notion of elegance is perhaps a little oversighted. In languages like Haskell and Idris, where anonymous functions are extremely common (and there is no function keyword!), such a construction would suck up space on a line. Consider this contrived example where we want to define the `const` function: it takes a value `x`, and returns a function which ignores its argument and returns `x`.

```
# keyword style (vaguely Gleam)
let const x = fun(_) { x }

# keyword style (vaguely ML)
let const x = fun _ -> x

# haskell(ish) style
let const x = \_ -> x
```

Here, the difference is small, but small amounts of wasted space can really add up; this is especially true if you expect users to constrain their code to 80 columns, as is typical in many languages. Especially when you consider the much more verbose Gleam-style example, I struggle to see how this works in a language where you want to treat functions as first-class citizens.

In the single most-ironic-possible twist, __Java__ is shockingly minimal in its anonymous function syntax: it uses the most obvious imperative analog to the Haskell-style, replacing the backslash with parentheses, and adds commas to delimit parameters. Clearly, this works well in general – Julia adopted this syntax, and dropped the horrific MATLAB syntax that it would otherwise have inherited.

Finally, a node on the various delimiters between the parameters and the function body. With the notable exceptions of Gleam (which uses curly-braces to delimit the function body), and Idris and Scala (which both use `=>` in place of `->`), every functional language uses `->` to mark the end of the parameter declarations and the beginning of the function body. Breaking with this tradition requires clear intent, though I confess that I think the `=>` syntax looks much better.

## Homoiconicity Is For Lisps and Mathematics
The appeal of the keyword-style is that it's natural, and --- with a little experience --- intuitive. To throw in some jargon, languages which follow this principle and reuse syntax whenever possible are called _homoiconic_; treating this property as sacrosanct will eventually draw you into writing a Lisp.

But I think holding to a single design principle like this is detrimental. Sure, Ruby probably went too far in the other direction, and C++ is a lovecraftian nightmare, but the central premise of a language is to be _useful_ --- not an exercise in mathematical purity.

The point of using anonymous function syntax is to be terse and brief; to write functions that don't really belong in the global scope; to make function literals as first class as string literals.
