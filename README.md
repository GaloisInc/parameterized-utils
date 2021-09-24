# Overview

The parameterized-utils module contains a collection of typeclasses
and datatypes for working with parameterized types, that is types that
have a type argument.  One example would be a algebraic data type
for expressions, that use a type parameter to describe the type of the
expression.

This packaged provides collections classes for these parameterized types.

# Parameterized Types Motivation

Parameterized types are types with a single type parameter.  One use of the type
parameter is to embed the type system of an AST into Haskell, in order to have
the Haskell compiler provide static guarantees of correctness.  The notion of
parameterized types in this library is similar to that of the singletons
library, but in some ways more flexible but less automated.

## A Simple Example

As an example of a parameterized type, consider the following:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
data EmbeddedType = EInt | EBool

data Expr (tp :: EmbeddedType) where
  IntLit :: Int -> Expr 'EInt
  BoolLit :: Bool -> Expr 'EBool
  Add :: Expr 'EInt -> Expr 'EInt -> Expr 'EInt
  Lt :: Expr 'EInt -> Expr 'EInt -> Expr 'EBool
```

The `Expr` type is a parameterized type, as it has a single type parameter.  The
GADT uses the type parameter to embed a simple type system into the language.
The datakind `EmbeddedType` is used as a type index.  GADT use comes with some
potential challenges, depending on use case.  Creating collections of values of
this `Expr` type can be slightly tricky due to the type parameter.

Attempting to define the value `[IntLit 5, BoolLit False]` results in a type
error because the two terms in the list have different types: `Expr 'EInt` and
`Expr 'EBool`, respectively.

One option is to existentially quantify away the type parameter.  There is a
helper type, `Some`, defined in Data.Parameterized.Some that does just this:
`[Some (IntLit 5), Some (BoolLit False)] :: [Some Expr]`.  Because `Expr` is
defined as a GADT, pattern matching on constructors allows us to recover the
type parameter.

Another option is to use a container designed to accommodate parameterized
types, such as `List` defined in Data.Parameterized.List.  This would look
something like `(IntLit 5 :< BoolLit False :< Nil) :: List Expr '[EInt, EBool]`.
Note that the type-level list reflects the types of the terms, allowing for some
powerful indexing and traversal patterns.

## An Extended Example

In the previous example, it is possible to recover the type parameters after
they have been existentially quantified away by pattern matching.  In a more
complicated example, that is not always possible:

```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
data EmbeddedType = EInt | EBool

data Expr (tp :: EmbeddedType) where
  IntLit :: Int -> Expr 'EInt
  BoolLit :: Bool -> Expr 'EBool
  Add :: Expr 'EInt -> Expr 'EInt -> Expr 'EInt
  Lt :: Expr 'EInt -> Expr 'EInt -> Expr 'EBool
  IsEq :: Expr tp -> Expr tp -> Expr 'EBool
```

In this case, pattern matching on the `IsEq` constructor does *not* recover the
types of the operands.  `IsEq` is polymorphic, so the parameters could either be
of type `EBool` or `EInt`, though we do learn that the types of the sub-terms
must at least be the same.  We could pattern match on those sub-terms
individually, but doing so might introduce an unpredictable amount of recursion
and significantly complicate the code.  One way to solve this issue is to
introduce run-time type representatives to allow us to more easily recover types.
```haskell
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
data EmbeddedType = EInt | EBool

data Repr tp where
  IntRepr :: Repr 'EInt
  BoolRepr :: Repr 'EBool

data Expr (tp :: EmbeddedType) where
  IntLit :: Int -> Expr 'EInt
  BoolLit :: Bool -> Expr 'EBool
  Add :: Expr 'EInt -> Expr 'EInt -> Expr 'EInt
  Lt :: Expr 'EInt -> Expr 'EInt -> Expr 'EBool
  IsEq :: Repr tp -> Expr tp -> Expr tp -> Expr 'EBool
```

The new type, `Repr`, is a singleton type that establishes a connection between
a run-time value and a type.  When we pattern match on `IsEq`, we can simply
inspect (i.e., pattern match on) the contained `Repr` value to determine the
types of the sub-terms:

```haskell
withBoolExprs :: Expr tp -> a -> ([Expr 'EBool] -> a) -> a
withBoolExprs e def k =
  case e of
    BoolLit {} -> k [e]
    Lt {} -> k [e]
    IsEq rep e1 e2
      | Just Refl <- testEquality rep BoolRepr ->
          -- Because we used a GADT pattern match, we know that tp ~ EBool
          k [e, e1, e2]
      | otherwise -> def
    _ -> def
```

# Package Structure

This package provides three main types of functionality:

* Typeclasses mirroring core Haskell classes, but adapted to parameterized types
* Data structures suitable for holding values of parameterized types
* Utilities for working with parameterized types, including tools for proving properties at the type level (dependently-typed programming in Haskell)

## Typeclasses

* Data.Parameterized.Classes

  This module contains a number of basic classes lifted to parameterized types,
  including `EqF`, `OrdF`, `ShowF`, and `HashableF`.  It also re-exports
  a few types from base that are useful for working with parameterized types,
  including `TestEquality`.

  The related module Data.Parameterized.TH.GADT provides Template Haskell
  functions to automatically implement instances of some of these classes.

* Data.Parameterized.ClassesC

  This module defines classes like Data.Parameterized.Classes, except that the
  class methods accept an additional parameter for comparing sub-terms.

* Data.Parameterized.TraversableFC

  This module generalizes `Functor`, `Foldable`, and `Traversable` to
  parameterized types.  In these operations, type parameters must be preserved.

* Data.Parameterized.TraversableF

  This module is like Data.Parameterized.TraversableFC, but intended for types
  that have a single parametric type parameter, rather than two.  The most
  common use of these functions and classes is with the `MapF` type described
  below.


## Data Structures

This package provides data structures that are either lifted to hold
parameterized types or otherwise type indexed.  The following modules implement
data structures:

* Data.Parameterized.Context (`Assignment (f :: k -> Type) (ctx :: Ctx k)`)

  `Assignment` is a sequence type that holds values of parameterized types.  It
  is essentially a snoc list (i.e., a list that is extended on the right instead
  of the left).  The `Ctx` (Context) type is a type-level snoc list.  In the
  default implementation, indexing is O(log(n)) time and total.

  There are technically two implementations of `Assignment`: a safe
  implementation based on a snoc list in pure Haskell and the default
  implementation based on a balanced binary tree that uses `unsafeCoerce` to
  manipulate type indexes for efficiency.  The safe implementation is a proof
  that the API presented is safe, while the unsafe implementation is efficient
  enough to use in practice.

* Data.Parameterized.List (`List (f :: k -> Type) [k]`)

  `List` is the plain Haskell list lifted to hold values of parameterized
  types.  Moreover, it uses the data kind lifted list syntax instead of the
  `Ctx` type.  Indexing into `List` is total but O(n).

* Data.Parameterized.Map (`MapF (key :: k -> Type) (value :: k -> Type)`)

  `MapF` an associative map from keys to values where both keys and values are
  parameterized types.  The lookup operation is O(log(n)), and recovers the type
  parameter of the value during lookup.

* Data.Parameterized.HashTable (`HashTable s (key :: k -> Type) (value :: k -> Type)`)

  `HashTable` is an associative container like `MapF`, except is mutable in
  `ST` (or `IO` via `stToIO`) due to the `s` type parameter.

* Data.Parameterized.Vector (`Vector (n :: Nat) (a :: Type)`)

  This module implements a length-indexed vector.  Unlike the other data
  structures in parameterized-utils, the type parameter only describes the
  length of the vector as a type-level natural; the elements in the vector do
  not have type indexes.

Additionally:

* Data.Parameterized.Pair (`data Pair a b = forall tp . Pair (a tp) (b tp)`)

  This module provides an existentially-quantified pair where both types in the
  pair are indexed by the same existentially quantified parameter.  Pattern
  matching on the constructor recovers the equality.  This type is primarily
  used in Data.Parameterized.Map, but is sometimes separately useful.

  Note that there is another useful notion of type parameterized pair, which is
  provided by Data.Functor.Product in base: `data Product a b tp = Pair (a tp)
  (b tp)`.  The difference is that the type parameter of `Product` is made
  manifest in the type, and thus is not quantified away.

## Utilities

* Data.Parameterized.NatRepr

  This module provides run-time representative values for natural numbers lifted
  to the type level, as well as some utilities for proving properties over
  type-level naturals.

* Data.Parameterized.Peano

  This module provides an implementation of type-level Peano numbers, as well as
  run-time representative values for them.  It also provides some utilities for
  proving properties over Peano numbers.

* Data.Parameterized.Fin

  `Fin n` is a finite type with `n` (terminating/non-bottom) inhabitants. It can
  be used to index into a `Vector n` or other size-indexed datatype.

* Data.Parameterized.SymbolRepr

  This module provides run-time representative values for strings lifted to
  the type level (symbols).

* Data.Parameterized.BoolRepr

  This module provides run-time representative values for booleans lifted to
  the type level.

* Data.Parameterized.Some

  The `Some` type is a wrapper that existentially quantifies away the type
  parameter of a parameterized value.  This can be used on any value with a
  parameterized type, but is most useful when an operation exists to recover the
  type parameter later (either via pattern matching over a GADT or by consulting
  a run-time type representative value).

* Data.Parameterized.Nonce

  `Nonce` is a parameterized type backed by a `Word64`.  Its `TestEquality`
  instance uses `unsafeCoerce` to allow the type parameter to be recovered.
  Similarly to a cryptographic nonce, the `Nonce` type is safe as long as no
  nonce value is reused.
