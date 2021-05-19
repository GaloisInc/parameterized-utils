{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Unsafe #-}
{-|
Copyright        : (c) Galois, Inc 2014-2021

An unsafe module that provides functionality for constructing equality proofs
that GHC cannot prove on its own.
-}
module Data.Parameterized.Axiom
  ( unsafeAxiom, unsafeHeteroAxiom
  ) where

import Data.Type.Equality
import Unsafe.Coerce (unsafeCoerce)

-- | Assert a proof of equality between two types.
-- This is unsafe if used improperly, so use this with caution!
unsafeAxiom :: forall a b. a :~: b
unsafeAxiom = unsafeCoerce (Refl @a)
{-# NOINLINE unsafeAxiom #-} -- Note [Mark unsafe axioms as NOINLINE]

-- | Assert a proof of heterogeneous equality between two types.
-- This is unsafe if used improperly, so use this with caution!
unsafeHeteroAxiom :: forall a b. a :~~: b
unsafeHeteroAxiom = unsafeCoerce (HRefl @a)
{-# NOINLINE unsafeHeteroAxiom #-} -- Note [Mark unsafe axioms as NOINLINE]

{-
Note [Mark unsafe axioms as NOINLINE]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We take care to mark definitions that use unsafeCoerce to construct proofs
(e.g., unsafeAxiom = unsafeCoerce Refl) as NOINLINE. There are at least two
good reasons to do so:

1. On old version of GHC (prior to 9.0), GHC was liable to optimize
   `unsafeCoerce` too aggressively, leading to unsound runtime behavior.
   See https://gitlab.haskell.org/ghc/ghc/-/issues/16893 for an example.

2. If GHC too heavily optimizes a program which cases on a proof of equality,
   where the equality is between two types that can be determined not to be
   equal statically (e.g., case (unsafeAxiom :: Bool :~: Int) of ...), then the
   optimized program can crash at runtime. See
   https://gitlab.haskell.org/ghc/ghc/-/issues/16310. Using NOINLINE is
   sufficient to work around the issue.
-}
