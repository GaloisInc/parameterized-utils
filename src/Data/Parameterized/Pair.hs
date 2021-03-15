{-|
Description : A 2-tuple with identically parameterized elements
Copyright   : (c) Galois, Inc 2017-2019

This module defines a 2-tuple where both elements are parameterized over the
same existentially quantified parameter.

-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
module Data.Parameterized.Pair
  ( Pair(..)
  , fstPair
  , sndPair
  , viewPair
  ) where

import Data.Kind
import Data.Parameterized.Classes
import Data.Parameterized.Some
import Data.Parameterized.TraversableF

-- | Like a 2-tuple, but with an existentially quantified parameter that both of
-- the elements share.
data Pair (a :: k -> Type) (b :: k -> Type) where
  Pair :: !(a tp) -> !(b tp) -> Pair a b

instance (TestEquality a, EqF b) => Eq (Pair a b) where
  Pair xa xb == Pair ya yb =
    case testEquality xa ya of
      Just Refl -> eqF xb yb
      Nothing -> False

instance FunctorF (Pair a) where
  fmapF f (Pair x y) = Pair x (f y)

instance FoldableF (Pair a) where
  foldMapF f (Pair _ y) = f y
  foldrF f z (Pair _ y) = f y z

-- | Extract the first element of a pair.
fstPair :: Pair a b -> Some a
fstPair (Pair x _) = Some x

-- | Extract the second element of a pair.
sndPair :: Pair a b -> Some b
sndPair (Pair _ y) = Some y

-- | Project out of Pair.
viewPair :: (forall tp. a tp -> b tp -> c) -> Pair a b -> c
viewPair f (Pair x y) = f x y
