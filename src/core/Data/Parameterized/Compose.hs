{-|
Description : utilities for working with "Data.Functor.Compose"
Copyright   : (c) Galois, Inc 2014-2019
Maintainer  : Langston Barrett <langston@galois.com>

Utilities for working with "Data.Functor.Compose".

NB: This module contains an orphan instance. It will be included in GHC 8.10,
see https://gitlab.haskell.org/ghc/ghc/merge_requests/273 and also
https://github.com/haskell-compat/base-orphans/issues/49.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}
module Data.Parameterized.Compose
  ( testEqualityComposeBare
  ) where

import Data.Functor.Compose
import Data.Orphans () -- For the TestEquality (Compose f g) instance
import Data.Type.Equality

-- | The deduction (via generativity) that if @g x :~: g y@ then @x :~: y@.
--
-- See https://gitlab.haskell.org/ghc/ghc/merge_requests/273.
testEqualityComposeBare :: forall k l (f :: k -> *) (g :: l -> k) x y.
                           (forall w z. f w -> f z -> Maybe (w :~: z))
                        -> Compose f g x
                        -> Compose f g y
                        -> Maybe (x :~: y)
testEqualityComposeBare testEquality_ (Compose x) (Compose y) =
  case (testEquality_ x y :: Maybe (g x :~: g y)) of
    Just Refl -> Just (Refl :: x :~: y)
    Nothing   -> Nothing
