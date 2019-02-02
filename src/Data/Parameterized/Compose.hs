{-|
Copyright        : (c) Galois, Inc 2014-2018
Maintainer       : Langston Barrett <langston@galois.com

Utilities for working with "Data.Functor.Compose".

NB: This module contains an orphan instance.
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
import Data.Type.Equality

-- | The deduction (via generativity) that if @g x :~: g y@ then @x :~: y@.
--
-- See https://gitlab.haskell.org/ghc/ghc/merge_requests/273.
testEqualityComposeBare :: forall (f :: k -> *) (g :: l -> k) x y.
                           (forall w z. f w -> f z -> Maybe (w :~: z))
                        -> Compose f g x
                        -> Compose f g y
                        -> Maybe (x :~: y)
testEqualityComposeBare testEquality_ (Compose x) (Compose y) =
  case (testEquality_ x y :: Maybe (g x :~: g y)) of
    Just Refl -> Just (Refl :: x :~: y)
    Nothing   -> Nothing

testEqualityCompose :: forall (f :: k -> *) (g :: l -> k) x y. (TestEquality f)
                    => Compose f g x
                    -> Compose f g y
                    -> Maybe (x :~: y)
testEqualityCompose = testEqualityComposeBare testEquality

instance (TestEquality f) => TestEquality (Compose f g) where
  testEquality = testEqualityCompose
