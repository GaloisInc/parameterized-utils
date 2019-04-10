# Changelog for the `parameterized-utils` package

## 2.0 -- *2019 Apr 03*

  * Drop support for GHC versions prior to GHC 8.2
  * Various Haddock and module updates.
  * Data.Parameterized.Classes
    - Added function: `ordFCompose`
    - Added `OrdF` instance for `Compose`
  * Data.Parameterized.ClassesC
    - Marked as `Safe` haskell via pragma
    - Added `OrdC` instance for `Some`
  * Data.Parameterized.Compose
    - Update `testEqualityComposeBare` to be more kind-polymorphic.
    - Marked as `Safe` haskell via pragma
  * Data.Parameterized.Context
    - Added `diffIsAppend` function to extract the contextual
      difference between two `Context`s (as a `Diff`) as an `IsAppend`
      (new) data value if the left is a sub-context of the right.
  * Data.Parameterized.NatRepr
    - Change runtime representation from `Int` to `Natural`
    - Add function `intValue` to recover an `Int` from a `NatRepr`.
    - Add constructor function `mkNatRepr` to construct a `NatRepr`
      from a `Natural`.
    - Removed awkward backdoor for directly creating `NatRepr` values;
      the single needed internal usage is now handled internally.
  * Data.Parameterized.Peano
    - Newly added module.
    - Defines a type `Peano` and `PeanoRepr` for representing a
      type-level natural at runtime.
    - The runtime representation of `PeanoRepr` is `Word64`
    - Has both safe and unsafe implementations.
  * Data.Parameterized.WithRepr
    - Newly added module.
    - This module declares a class `IsRepr` with a single method
      `withRepr` that can be used to derive a 'KnownRepr' constraint
      from an explicit 'Repr' argument. Clients of this method need
      only create an empty instance. The default implementation
      suffices.

## 1.0.8 -- *2019 Feb 01*

  * Data.Parameterized.Map
    - Fixed `MapF` functions `filter` and `filterWithKey`
    - Added `MapF` function: `mapWithKey`
  * Data.Parameterized.NatRepr
    - Un-deprecate `withKnownNat`
  * Data.Parameterized.Context
    - Updated some haddock documentation (esp. `CtxEmbedding` data structure).
  * Data.Parameterized.Nonce
    - Fixed `newIONonceGenerator` haddock documentation (IO monad, not ST monad).
    - Added `countNoncesGenerated` for profiling Nonce usage.
  * Data.Parameterized.TraversableF
    - Added `FunctorF`, `FoldableF`, and `TraversableF` instances for
      `Compose` from Data.Functor.Compose
  * Data.Parameterized.ClassesC
    - Newly added module.
    - Declares `TestEqualityC` and `OrdC` classes for working with
      types that have kind `(k -> *) -> *` for any `k`.
  * Data.Parameterized.Compose
    - Newly added module.
    - Orphan instance and `testEqualityComposeBare` function for
      working with Data.Functor.Compose.
  * Data.Parameterized.TestEquality
    - Newly added module.
    - Utilities for working with Data.Type.TestEquality.

## 1.0.7 -- *2018 Nov 17*

  * Data.Parameterized.Map
    - Added `MapF` functions:
      - `filter`
      - `filterWithKey`

## 1.0.6 -- *2018 Nov 19*

  * Add support for GHC 8.6.
  * Data.Parameterized.Map
    - Added functions:
       - `foldlWithKey` and `foldlWithKey'` (strict)
       - `foldrWithKey` and `foldrWithKey'` (strict)
       - `mapMaybeWithKey`

## 1.0.5 -- *2018 Sep 04*

  * Data.Parameterized.Context
      - Add function: `take`, `appendEmbedding`, `appendDiff`
      - Diff is type role nominal in both parameters.

## 1.0.4 -- *2018 Aug 29*

  * Data.Parameterized.Context
    - Add `traverseAndCollect`.  Allows traversal of an Assignment in
      order from left to right, collecting the results of a visitor
      function monoidically.
  * Data.Parameterized.DecidableEq
    - Newly added module.  The `DecidableEq` class represents
      decideable equality on a type family as a superclass of
      `TestEquality`, where the latter cannot provide evidence of
      non-equality.
  * Data.Parameterized.NatRepr
    - Add `DecidableEq` instance for NatRepr.
    - Add functions:
      - `decideLeq`
      - `isZeroOrGT1`
      - `lessThanIrreflexive`
      - `lessThanAsymmetric`
      - `natRecStrong`  -- recursor with strong induction
      - `natRecBounded` -- bounded recursor
      - `natFromZero`
  * Data.Parameterized.Vector
    - Add construction functions: `singleton`, `cons`, `snoc`, `generate`, and `generateM`
    - Add functions: `splitWithA` (applicative `splitWith`).

## 1.0.3 -- *2018 Aug 24*

  * Move `lemmaMul` from Vector to NatRepr.
  * Add stricter role annotations:
    - `NatRepr` is nominal.
    - `Vector` is nominal in the first parameter and representational in the second.
  * Data.Parameterized.NatRepr
    - Provide a backdoor for directly creating `NatRepr` values.  Use carefully.
  * Data.Parameterized.Vector
    - Add Show and Eq instances
    - Add functions: `joinWithM`, `reverse`

## 1.0.2 -- *2018 Aug 23*

  * Allow function passed to `traverseF_`, `traverseFC_`, and
    `forMFC_` to return a value instead of null (`()`).
  * Data.Parameterized.Vector
    - Newly added module.  A fixed-size vector of typed elements.
  * Data.Parameterized.Utils.Endian
    - Newly added module.  Used in Vector.

## 1.0.1 -- *2018 Aug 13*

  Baseline for changelog tracking.
