# Higher-Ranked Polymorphism
> Refer in particular to [this post](https://cohost.org/prophet/post/1757240-higher-rank-polymorp) from Prophet (welltypedwitch).

Functions in Haskell can use higher-ranked polymorphism --- they are permitted to take polymorphic types as parameters and instantiate them with multiple different concrete types.

```haskell
-- this example was given in prophet's post

f : (forall a. a -> a) -> (Int, String)
f(g) = (g(5), g("AAA"))
```

From the perspective of a Rust programmer, this behaviour struck me as odd; though from the perspective of Haskell's type system, it's perfectly acceptable.

GHC compiles this code using type erasure, so the invocations of `g` just become lookups in a virtual table. This is (debatably) fine in most cases, but it's a potential performance nightmare if `f` ever gets called in the hot path.

I'm **far** more inclined to disallow this kind of higher-ranked polymorphism, which would imply a [predicative](https://en.wikipedia.org/wiki/Parametric_polymorphism#Rank-1_(predicative)_polymorphism) type system in the style of ML. In no small part, this is because requiring functions to have concrete types allows for aggressive monomorphisation of the kind found in `rustc`.

The incidental advantage is that predicative type systems need fewer type annotations in general.
