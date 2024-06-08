# Interfaceless Interfaces
> like, what even ***are*** interfaces, man?

## Background
All (modern) programming languages have some way to express generic code, largely because (1) it helps to minimise code duplication and (2) can abstract away differences between relatively similar objects/types/patterns.

In the context of functional programming, generic facilities arise largely as _interfaces_.[^1] An interface is usually a collection of functions, constants, and associated types; conceptually this is equivalent to a collection of _only_ functions, and so this is the case we will consider.

We can view interfaces as examples of _ad-hoc polymorphism_ (in contrast with _parametric_ polymorphism), since they permit the implementation of a given function to change dramatically based on the given types and inferred return type.

## Julian Functions
The core issue is as follows: **almost all interfaces have a single function**.

That is, if interfaces are really just sets of functions, and if most interfaces contain just a single function, then what is the utility of an interface beyond being an awkward kind of access specifier?

The clearest answer to this question comes in the form of Julia, which does not have interfaces, and instead handles parametric and ad-hoc polymorphism with the notion of _methods_.

In Julia, a single function may have several _methods_; these are instances of the function that are uniquely identified by their input types. When a function is called, the runtime first finds the "most specific" method for the supplied parameter types, and then passes this to the LLVM backend.

Julia's system does have some components that would be awkward in the context of a primarily AOT-compiled language; for example, the issue of _type piracy_ can't be addressed with something like Rust's orphan rule, and so there's always a risk that importing a new module could cause totally unrelated code to break.[^2] Also, there's no way for a function to constrain the signature of its methods, and there's no way to express functionally dependent input parameter types as in Rust.

But, my suspicion is that this system is incredibly powerful, and moreover that this power can be almost entirely kept out of view of first-time learners. Even more, this kind of generic code does away with **enormous** quantities of boilerplate; it is the difference between this Rust code:

```rust
use std::fmt;

impl fmt::Display for CustomType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // ... some implementation ...
    }
}
```

And this Julia code:

```julia
show(io::Core.io, value::CustomType) = some_implementation(...)
```

## Issues
### Associated Types (Functional Type Dependencies)
### Method Resolution
### Specialisation
```
// io and a are free type parameters
// Result<T, E> is a generic type (with kind * -> * -> *)
// () is the unit type
// Error is an associated type (marked by the assoc keyword)
function display : io -> a -> Result<(), assoc Error>

// generic instance for a fixed io = Console
// the type of value is omitted and left "as generic as possible"
// the type of value has a string instance (inferred constraint)
// console.to_stdout has the signature String -> Result<(), ConsoleError>
// Error = ConsoleError (inferred constraint)
display(console: Console, value) = console.to_stdout(string(value))

// with currying syntax, the above instance could be written like this
// where . is the composition operator (could also be ∘ as in Julia)
display(console: Console) = console.to_stdout . string
```
### Function Constraints
`TODO:` discuss (1) how Julia functions have no constraints, and (2) how you could model the usual components of an interface in terms of function constraints.

### Higher-Kinded Types

## Notes
### Comorbid Functions Are Strict Constraints
This is quite an involved example, but it illustrates the point well.

Consider a Haskell type class `Biapplicative` that generalises the notion of an applicative functor to bifunctors.

```haskell
class Bifunctor p => Biapplicative p where
    bipure  :: a -> b -> p a b
    -- pronounced "biap"
    (<<*>>) :: p (a -> c) (b -> d) -> p a b -> p c d
```

It's fairly simple to write out, though perhaps unnecessarily abstract. It helps to think of this type class in terms of the implementation for the `Pair` type (hence the `p`).

```haskell
Biapplicative Pair where
    bipure         = (,)
    (<<*>>) (f, g) = bimap f g
```

Great! All this really gives us is a way to make pairs of values, and a way to apply pairs of functions to pairs of values. But having just one instance of a type class is effectively pointless, so what about the other common bifunctor: `Either`?

Try it! Ultimately, you're going to run into the problem that we created by writing `Biapplicative` in the first place: how do you write `bipure` for `Either l r`? You're going to get a value of type `l`, and a value of type `r`, and you have no choice in the matter: *you must discard at least one of them*.

Irritatingly, there ***is*** a relatively obvious implementation for `(<<*>>)`.

```haskell
(<<*>>) (Left  f) = bimap f id
(<<*>>) (Right f) = bimap id f
```

But we locked ourselves into this structure: to implement `<<*>>`, we are obliged to implement `bipure`, even though there isn't a sensible implementation for `Either`.

I would argue that *this* is the reason why so many interfaces in the real world consist of just one function. To fix this issue, we can do exactly that: break `Biapplicative` into two type classes, one for each function, and then just make `Biapplicative` into a marker class.

```haskell
class Bifunctor p => Bipure p where
    bipure :: a -> b -> p a b

class Bifunctor p => Biapply p where
    (<<*>>) :: p (a -> c) (b -> d) -> p a b -> p c d

-- now Biapplicative is just a marker
class Bipure p => Biapply p => Biapplicative p

Bipure Pair where
    bipure = (,)

Biapply Pair where
    (<<*>>) (f, g) = bimap f g

-- this is an (arguably) redundant opt-in clause
Biapplicative Pair

-- now we can write the version of <<*>> for Either!
Biapply Either where
    (<<*>>) (Left  f) = bimap f id
    (<<*>>) (Right f) = bimap id f
```

A note: there's a fairly compelling argument that says the `Biapplicative Pair` fragment is *not* redundant. In the context of Haskell's type-class-based type system, marker classes can help control the types that can participate in particular "ecosystems." This is echoed in the Rust world, where the compiler uses marker traits to reason about the safety properties of many types.

I'd argue that this reflects how baked-in traits and type classes are in their respective languages, but also a design blind spot --- in the absence of sufficiently fine-grained access control schemes, users will coopt any available method to make strong guarantees about their APIs.

## Resources
- [Chalk](https://rust-lang.github.io/chalk/book/), an implementation of Rust's trait system as a logic solver.


[^1]: The terms _trait_, _type class_, and _interface_ are broadly interchangeable.
[^2]: I suspect there are _at least_ a few CVEs waiting to be found in this system.
