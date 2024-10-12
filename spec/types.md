# Types

## Primitive Types
The primitive types are:
1. `!` (pronounced _never_)
2. `()` (pronounced _unit_)
3. `bool`
4. `char`
5. `string`
6. `int`
7. `float`

### Never
The never type `!` is the canonical 0-type. It has no terms, and 
is uninhabited.

### Unit
The unit type `()` is the canonical 1-type. It has a single term `()`.

### Bool
The boolean type `bool` is the canonical 2-type. It has two terms, 
`true` and `false`.

### Characters
The character type `char` represents a single Unicode scalar value.

### Strings
The string type `string` represents a valid sequence of Unicode codepoints.
While it is not defined to be a sequence of `char` terms, it is guaranteed that
a `string` term can always be losslessly decomposed into a `char` sequence.

### Integers
The integer type `int` represents a signed integer. The size and range of an
`int` is architecture-dependent, but is guaranteed to be at least `w ≥ 24` bits
and to contain the range `[-2^(w-1), 2^(w-1) - 1]`. Storing a value outside
this range is undefined behaviour.

Arithmetic underflow and overflow are well-defined operations, and do not
cause runtime errors.

### Floats
The float type `float` represents an IEEE-754 64-bit floating-point number,
and incurs all the expectations and behaviours that the standard defines.

## Composite Types
The composite types are:
1. Tuples
2. Functions
3. Named Types

### Tuples
A tuple type is an ordered finite sequence of types. The terms of a tuple type
are ordered finite sequences of terms, where the type of each term is given by
the corresponding type in the same position in the tuple type.

The unit type is not considered to be a tuple type. A tuple type must contain
at least two operand types, and so the singleton tuple also cannot exist.

### Functions
A function type is a type of the form `(A, B, C,...) -> Ret`. The lefthand side
of the `->` operator is called the _domain_, while the righthand side is called
the _codomain_. In the special case where the domain contains only one element
`A`, the parentheses may be elided and the type may be written `A -> Ret`.

The `->` operator is right-associative, so the type `A -> B -> C` is equivalent
to the type `A -> (B -> C)`.

While the type `() -> Ret` denotes a unary function from `()` to `Ret`, it can
be interpreted as a nullary function to `Ret`. In practice, these two views are
equivalent, and so it is permissible to treat such a function in both ways: it
may be called as `f(())`, or just `f()`.

### Named Types
Named types are either structures or enumerations, defined with the `struct`
and `enum` keywords respectively. These constructions are dual, and correspond
to _product_ and _coproduct_ types.

#### Structures
A structure has a name, optionally some generic parameters, and a set of fields
which each consist of a name and a type. A structure has a single constructor,
and this constructor takes values for all the fields of the structure. If a
structure has no fields, then it is a singleton and isomorphic to `()`.

Formally, structures are product types. For typechecking purposes, they are
treated as enumerations with a single constructor whose arguments are a
tuple of the record's field types.

A structure field may be marked as `mutable`, in which case the `<-` operator
can be used to update the value of the field.

#### Enumerations
An enumeration has a name, optionally some generic parameters, and a set of
constructors. The constructors are scoped in a module whose name is exactly
the same as the name of the enumeration. Each constructor may have a payload,
which may take one or more arguments. If an enumeration has no constructors,
then it has no terms and is isomorphic to `!`.

Formally, enumerations are coproduct types. For typechecking purposes, the
constructors of an enumeration are treated as always having a payload, and
this payload is always a single type.
