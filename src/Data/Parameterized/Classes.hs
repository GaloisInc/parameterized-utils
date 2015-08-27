------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Classes
-- Description      : Declares classes for working with types containing
--                    a polymorphic parameter.
-- Copyright        : (c) Galois, Inc 2014-2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module declares classes for working with types with the kind
-- @k -> *@ for any kind @k@.  These are generalizations of the
-- @Data.Functor.Classes@ types as they work with any kind @k@, and are
-- not restricted to "*".
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
  ( -- * Equality exports
    Equality.TestEquality(..)
  , (Equality.:~:)(..)
  , EqF(..)
  , PolyEq(..)
    -- * Ordering generalization
  , OrdF(..)
  , OrderingF(..)
  , orderingF_refl
  , toOrdering
  , fromOrdering
    -- * Typeclass generalizations
  , ShowF(..)
  , HashableF(..)
  , CoerceableF(..)
    -- * Re-exports
  , Data.Maybe.isJust
  ) where

import Data.Maybe (isJust)
import Data.Type.Equality as Equality

-- | An instance of CoerceableF gives a way to coerce between
--   all the types of a family.  We generally use this to witness
--   the fact that the type parameter to rtp is a phantom type
--   by giving an implementation in terms of Data.Coerce.coerce.
class CoerceableF (rtp :: k -> *) where
  coerceF :: rtp a -> rtp b

-- | @EqF@ provides a method @eqF@ for testing whether two parameterized
-- types are equal.
--
-- Unlike @testEquality@, this only works when the type arguments are the
-- same, and does not provide a proof that the types has
-- the same type when they are equal, and thus this can be implemented
-- over parameterized types that are unable to provide the evidence they
-- are equal.
class EqF (f :: k -> *) where
  eqF :: f a -> f a -> Bool

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

orderingF_refl :: OrderingF x y -> Maybe (x :~: y)
orderingF_refl o =
  case o of
    LTF -> Nothing
    EQF -> Just Refl
    GTF -> Nothing

-- | Convert orderingF to standard ordering
toOrdering :: OrderingF x y -> Ordering
toOrdering LTF = LT
toOrdering EQF = EQ
toOrdering GTF = GT

-- | Convert standard ordering to OrderF
fromOrdering :: Ordering -> OrderingF x x
fromOrdering LT = LTF
fromOrdering EQ = EQF
fromOrdering GT = GTF

-- | A parameterized type that can be compared on distinct instances.
class TestEquality ktp => OrdF (ktp :: k -> *) where
  -- | compareF compares two keys with different type parameters.
  -- Instances must ensure that keys are only equal if the type
  -- parameters are equal.
  compareF :: ktp x -> ktp y -> OrderingF x y

  leqF :: ktp x -> ktp y -> Bool
  leqF x y =
    case compareF x y of
      LTF -> True
      EQF -> True
      GTF -> False

  ltF :: ktp x -> ktp y -> Bool
  ltF x y =
    case compareF x y of
      LTF -> True
      EQF -> False
      GTF -> False

  geqF :: ktp x -> ktp y -> Bool
  geqF x y =
    case compareF x y of
      LTF -> False
      EQF -> True
      GTF -> True

  gtF :: ktp x -> ktp y -> Bool
  gtF x y =
    case compareF x y of
      LTF -> False
      EQF -> False
      GTF -> True

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
