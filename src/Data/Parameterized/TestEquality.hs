{-|
Copyright        : (c) Galois, Inc 2014-2018
Maintainer       : Langston Barrett <langston@galois.com

Utilities for working with "Data.Type.TestEquality".

NB: This module contains an orphan instance.
-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

import Data.Functor.Compose
import Data.Type.Equality

testEqualityComposeBare :: forall f g x y.
                           (forall w z. f w -> f z -> Maybe (w :~: z))
                        -> Compose f g x
                        -> Compose f g y
                        -> Maybe (x :~: y)
testEqualityComposeBare testEquality_ (Compose x) (Compose y) =
  case (testEquality_ x y :: Maybe (g x :~: g y)) of
    Just Refl -> Just (Refl :: x :~: y)
    Nothing   -> Nothing

testEqualityCompose :: forall f g x y. (TestEquality f)
                    => Compose f g x
                    -> Compose f g y
                    -> Maybe (x :~: y)
testEqualityCompose = testEqualityComposeBare testEquality

-- | The deduction (via generativity) that if @g x :~: g y@ then @x :~: y@.
instance (TestEquality f) => TestEquality (Compose f g) where
  testEquality = testEqualityCompose
