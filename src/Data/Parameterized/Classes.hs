------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Classes
-- Description      : Declares classes for working with types containing a
--                    polymorphic parameter.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module declares classes for working with types with the kind @k -> *@ for
-- any kind @k@.  These are generalizations of the Data.Functor.Classes types as
-- they work with any kind @k@, and are not restricted to "*".
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.Classes
  ( Equality.TestEquality(..)
  , (Equality.:~:)(..)
  , PolyEq(..)
  , OrdF(..)
  , OrderingF(..)
  , toOrdering
  , FunctorF(..)
  , ShowF(..)
  , HashableF(..)
  , CoerceableF(..)
    -- * Re-exporrts
  , Data.Maybe.isJust
  ) where

import Data.Maybe (isJust)
import Data.Type.Equality as Equality

-- | An instance of CoerceableF gives a way to coerce between
--   all the types of a family.  We generally use this to witness
--   the fact that the type parameter to rtp is a phantom type
--   by giving an implementation in terms of Data.Coerce.coerce.
class CoerceableF (rtp:: k -> *) where
  coerceF :: rtp a -> rtp b

-- | A polymorphic equality operator that generalizes TestEquality.
class PolyEq u v where
  polyEqF :: u -> v -> Maybe (u :~: v)

  polyEq :: u -> v -> Bool
  polyEq x y = isJust (polyEqF x y)

-- | Ordering over two distinct types with a proof they are equal.
data OrderingF x y where
  LTF :: OrderingF x y
  EQF :: OrderingF x x
  GTF :: OrderingF x y

-- | Convert ordering1 to standard ordering
toOrdering :: OrderingF x y -> Ordering
toOrdering LTF = LT
toOrdering EQF = EQ
toOrdering GTF = GT

-- | A parameterized type that can be compared on distinct instances.
class TestEquality ktp => OrdF (ktp :: k -> *) where
  -- | compareF compares two keys with different type parameters.
  -- Instances must ensure that keys are only equal if the type
  -- parameters are equal.
  compareF :: ktp x -> ktp y -> OrderingF x y

-- | A parameterized type that is a function on all instances.
class FunctorF m where
  fmapF :: (forall x . f x -> g x) -> m f -> m g

-- | A parameterized type that can be shown on all instances.
class ShowF f where
  showF :: f tp -> String
  showF f = showsF f ""

  showsF :: f tp -> String -> String
  showsF f s = showF f ++ s

-- | A default salt used in the implementation of 'hash'.
defaultSalt :: Int
#if WORD_SIZE_IN_BITS == 64
defaultSalt = 0xdc36d1615b7400a4
#else
defaultSalt = 0x087fc72c
#endif
{-# INLINE defaultSalt #-}

-- | A parameterized type that is hashable on all instance.
class HashableF (f :: k -> *) where
  hashWithSaltF :: Int -> f tp -> Int

  -- | Hash with default salt.
  hashF :: f tp -> Int
  hashF = hashWithSaltF defaultSalt