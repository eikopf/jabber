# Nullary Functions
Suppose we define a nullary function signature `one`, and add some instances.

```
sig one : T

fn one() -> Int   = 1i
fn one() -> UInt  = 1u
fn one() -> Float = 1.0
```

Uniqueness is trivial, since we have only one type parameter, but type inference becomes annoying --- consider the following snippet.

```
// the (+) operator might have multiple instances with a
// type signature UInt -> T -> UInt, so how do we pick one?
const uint_14: UInt = 13u + one()

// using blocks, it's possible (but ugly) to add an explicit annotation
const uint_6: UInt = {
  let one_val: UInt = one()
  5u + one_val
}
```

Really, we want to approximate a function signature with the dependent type `(T : Type) -> T`, but this can't be written in an ordinarily-typed function signature. The obvious answer is some form of inline type annotation, like the turbofish.

```
// some candidates
one::<T>()  // turbofish
one<T>()    // Java-style
one{T}()    // Julia-style
one()::T    // Haskell-style
(one() : T) // OCaml-style

// how would this extend to more complex functions?
sig foo : A -> B -> C

// extended Julia-style
foo{T -> U -> V}()
foo{T -> _}()
foo{_ -> _ -> V}()

// extended OCaml-style
(foo() : T -> U -> V)
(foo() : T -> _)
(foo() : _ -> _ -> V)
```

Despite introducing some parsing ambiguities, I prefer the OCaml style the most; it avoids having to bind type parameters in a particular order so that they can be addressed, as in the Rust-style turbofish syntax.
