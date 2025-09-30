# Changelog for the `parameterized-utils` package

## next

  * Replace dependency on `lens` with `microlens` and `microlens-pro`.

## 2.1.11.0 -- *2025 Nov 4*

  * Add support for GHC 9.12.

## 2.1.10.0 -- *2025 Mar 20*

  * New instances for types from `base`:

    - `{Functor,Foldable,Traversable}F` instances for `Product`, `Proxy`, `Sum`
    - `{Functor,Foldable,Traversable}FC` instances for `Alt`, `Ap`

  * `{Functor,Foldable,Traversable}FC` instances for `TypeAp`

  * `EqF` instances for `Assignment`, `BoolRepr`, `Index`, `List`, `NatRepr`,
    `Nonce`, `PairRepr`, `PeanoRepr`, and `SymbolRepr`

## 2.1.9.0 -- *2024 Sep 19*

  * Add support for GHC 9.10.

## 2.1.8.0 -- *2023 Jan 15*

  * Add support for GHC 9.8.
  * Allow building with `constraints-0.14.*`, `tasty-1.5.*`, and
    `th-abstraction-0.6.*`.

## 2.1.7.0 -- *2023 Jul 28*

  * Add support for GHC 9.6.
  * Allow building with `base-orphans-0.9.*`, `mtl-2.3.*`, and
    `th-abstraction-0.5.*`.
  * Mark `Data.Parameterized.ClassesC` as `Trustworthy` to restore the ability
    to build `parameterized-utils` with versions of `lens` older than `lens-5`.

## 2.1.6.0 -- *2022 Dec 18*

  * Added `FinMap`: an integer map with a statically-known maximum size.
  * Added `someLens` to `Some` to create a parameterized lens.
  * Allow building with `hashable-1.4.*`. Because `hashable-1.4.0.0` adds an
    `Eq` superclass to `Hashable`, some instances of `Hashable` in
    `parameterized-utils` now require additional `TestEquality` constraints, as
    the corresponding `Eq` instances for these data types also require
    `TestEquality` constraints.
  * Bump constraints to allow: vector-0.13, lens-5.2, tasty-hedgehog-1.3.0.0--1.4.0.0, GHC-9.4

## 2.1.5.0 -- *2022 Mar 08*

  * Add support for GHC 9.2.  Drop support for GHC 8.4 (or earlier).
  * Add a `Data.Parameterized.NatRepr.leqZero :: LeqProof 0 n` function.
    Starting with GHC 9.2, GHC is no longer able to conclude that
    `forall (n :: Nat). 0 <= n` due to changes in how the `(<=)` type family
    works. As a result, this fact must be asserted as an axiom, which the
    `leqZero` function accomplishes.

## 2.1.4.0 -- *2021 Oct 1*

  * Added the `ifoldLM` and `fromSomeList`, `fromListWith`, and
    `fromListWithM` functions to the `List` module.
  * Fix the description of the laws of the `OrdF` class.
  * Fix a bug in which `Data.Parameterized.Vector.{join,joinWith,joinWithM}`
    and `Data.Parameterized.NatRepr.plusAssoc` could crash at runtime if
    compiled without optimizations.
  * Add a `Data.Parameterized.Axiom` module providing `unsafeAxiom` and
    `unsafeHeteroAxiom`, which can construct proofs of equality between types
    that GHC isn't able to prove on its own. These functions are unsafe if used
    improperly, so the responsibility is on the programmer to ensure that these
    functions are used appropriately.
  * Various `Proxy` enhancements: adds `KnownRepr`, `EqF`, and `ShowF` instances.
  * Adds `mkRepr` and `mkKnownReprs` Template Haskell functions.
  * Added `TraversableFC.WithIndex` module which provides the
    `FunctorFCWithIndex`, `FoldableFCWithIndex`, and
    `TraversableFCWithIndex` classes, with instances defined for
    `Assignment` and `List`.
  * Added `indicesUpTo`, and `indicesOf` as well as `iterateN` and `iterateNM`
    for the `Vector` module.
  * Added `Data.Parameterized.Fin` for finite types which can be used
    to index into a `Vector n` or other size-indexed datatypes.


## 2.1.3.0 -- *2021 Mar 23*

  * Add support for GHC 9.
  * In the `Context` module:
    * Added `sizeToNatRepr` function for converting a `Context` `Size`.
    * Added `unzip` to unzip an `Assignment` of `Product(Pair)` into a
      separate `Assignment` for each element of the `Pair` (the
      inverse of the `zipWith Pair` operation).
    * Added `flattenAssignment` to convert an `Assignment` of
      `Assignment` into an `Assignment` of `CtxFlatten`.  Also adds
      `flattenSize` to combine the sizes of each context into the size
      of the corresponding `CtxFlatten`.
  * In the `Vector` module:
    * Added `fromAssignment` and `toAssignment` to allow conversions
      between `Assignment` and `Vector`.
    * Added `unsnoc`, `unfoldr`, `unfoldrM`, `unfoldrWithIndex`, and
      `unfoldrWithIndexM` functions.
  * Various haddock documentation updates and corrections.
  * Updated the Cabal specification to Cabal-version 2.2.


## 2.1.2 -- *2021 Jan 25*

  * Added `SomeSym` and `viewSomeSym` for existentially hidden Symbol
    values which retain the `KnownSymbol` constraint.
  * Added `leftIndex` and `rightIndex` for re-casting indexes of the
    individual parts of an Assignment into the concatenated
    Assignment.
  * Additional tests and updated documentation.

## 2.1.1 -- *2020 Jul 30*

  * Added `drop` and `appendEmbeddingLeft` functions to the `Context` module.
  * Fixes/updates to haddock documentation (fixing Issue #74).
  * Allow tasty v1.3 for testing (thanks to felixonmars)

## 2.1.0 -- *2020 May 08*

  * Added `plusAssoc` to the `NatRepr` module to produce `+` associativity evidence.
  * Changed the `HashTable` module to use the Basic instead of the Cuckoo
    implementation strategy.
  * Added explicit kind parameters to various definitions to support
    GHC 8.10's adoption of [proposal 103](https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0103-no-kind-vars.rst).
    This is a modification to the type signatures which _may impact_
    backward-compatibility and require updates, especially for any
    uses of
    [`TypeApplications`](https://gitlab.haskell.org/ghc/ghc/-/wikis/type-application).
  * No longer verifying support for GHC 8.2 or earlier.
  * Updated the minimum cabal version to 1.10 and specify the
    default-language as Haskell2010.

## 2.0.2 -- *2020 Feb 10*

  * Add the `dropPrefix` operation to `Context` which splits an `Assignment`.
  * Add `intersectWithKeyMaybe` and `mergeWithKey` to `Map`.
  * Add `mapAt`, `mapAtM`, and `replace` to `Vector`.
  * Add dependency on `base-orphans` to handle the `TestEquality`
    instance for `Compose`; needed for GHC 8.10.
  * Bump upper limit of `lens` dependency to allow 4.19.

## 2.0.1 -- *2019 Nov 06*

  * Documentation updates
  * Dependency constraint updates: constraints, lens, th-abstraction, hashable, hashtables, and vector.
  * Now supports building under GHC 8.8.1.
  * Added monadic folds and more traversals:
      * lazy folds: `foldlMF`, `foldrMF`, `foldlMFC`, `foldrMFC`
      * strict folds: `foldlMF'`, `foldrMF'`, `foldlMFC'`, `foldrMFC'`
      * `forF`, `forF_`
      * `forFC`, `forFC_`
      * `lengthF`
  * Added monadic folds, ascending or descending list conversions to `Parameterized.Map`:
      * Added monadic folds: `foldlMWithKey`, `foldrMWithKey`
      * Added ascending or descending list conversions: `toAscList` (equivalent to existing `toList`) and `toDescList`.
      * Added `findWithDefault` to lookup a key or return a default value.
      * Added `traverseMaybeWithKey`.
      * Fixes traverse to do an in-order rather than a pre-order traversal.
  * Added the `Data.Parameterized.All` module for universal quantification/parametricity over a type variable.
  * Additions to `Data.Parameterized.Context`:
      * Added `IndexView` type and `viewIndex` functions.
      * Added `addDiff` function to explicitly describe the (flipped) binary operator for the `Diff` instance of the `Category` class from `Control.Category`.
      * Added `traverseWithIndex_`
  * Added `Data.Parameterized.DataKind` providing the `PairRepr` type with associated `fst` and `snd` functions.
  * Added `TypeAp` to `Data.Parameterized.Classes`
  * Added `runSTNonceGenerator` to `Data.Parameterized.Nonce` for a *global* ST generator.
  * Added a `Hashable` instance for list `Index l x` types.
  * Changes in GADT TH code generator:
      * Added `structuralHashWithSalt` to
      * Fixed off by one bug in output
      * Fixed generation and constructor generation to use constructor type arguments, not type parameters.
  * The `Some` type is now an instance of `FunctorF`, `FoldableF`, and `TraversableF`.
  * Adjusted `structuralShowsPrec` precedence to match GHC derived `Show` instances.
  * The `Data.Parameterized.Nonce.Unsafe` module is now deprecated: clients should switch to `Data.Parameterized.Nonce`.

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
