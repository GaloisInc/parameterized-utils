{-# OPTIONS_HADDOCK ignore-exports #-}
{- above haddock option is a workaround for https://github.com/haskell/haddock/issues/310 #-}
------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.NatRepr
-- Description      : Data-type for representing a type-level Nat.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This defines a type @NatRepr@ for representing a type-level natural
-- at runtime.  This can be used to branch on a type-level value.  For
-- each @n@, @NatRepr n@ contains a single value containing the vlaue
-- @n@.  This can be used to help use type-level variables on code
-- with data dependendent types.
--
-- The @TestEquality@ instance for @NatRepr@ is implemented using
-- @unsafeCoerce@, as is the `isZeroNat` function. This should be
-- typesafe because we maintain the invariant that the integer value
-- contained in a NatRepr value matches its static type.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.NatRepr
  ( NatRepr
  , knownNat
  , IsZeroNat(..)
  , isZeroNat
  , decNat
  , incNat
  , addNat
  , halfNat
  , someNat
  , widthVal
  , maxNat
    -- * LeqProof
  , LeqProof(..)
  , knownLeq
  , testLeq
    -- * Re-exports typelists basics
  , NatK
  , type (+)
  , type (*)
  , type (<=)
  , Equality.TestEquality(..)
  , (Equality.:~:)(..)
  , Data.Parameterized.Some.Some
  ) where

import Control.Exception (assert)
import Data.Hashable
import Data.Proxy as Proxy
import Data.Type.Equality as Equality
import GHC.TypeLits as TypeLits
import Unsafe.Coerce

import Data.Parameterized.Classes
import Data.Parameterized.Some

intMax :: Int
intMax = maxBound

type NatK = Nat

------------------------------------------------------------------------
-- Nat

newtype NatRepr (n::Nat) = NatRepr { widthVal :: Int }
  deriving (Hashable)

instance Eq (NatRepr m) where
  _ == _ = True

instance TestEquality NatRepr where
  testEquality (NatRepr m) (NatRepr n)
    | m == n = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance PolyEq (NatRepr m) (NatRepr n) where
  polyEqF x y = fmap (\Refl -> Refl) $ testEquality x y

instance Show (NatRepr n) where
  show (NatRepr n) = show n

-- | This generates a NatRepr from a type-level context.
knownNat :: KnownNat n => NatRepr n
knownNat = go Proxy
  where go :: KnownNat n => Proxy n -> NatRepr n
        go p = assert (v <= toInteger intMax) (NatRepr (fromInteger v))
          where v = natVal p

data IsZeroNat n where
  ZeroNat    :: !(n :~: 0) -> IsZeroNat n
  NonZeroNat :: !(n :~: m+1) -> IsZeroNat n

isZeroNat :: NatRepr n -> IsZeroNat n
isZeroNat (NatRepr 0) = ZeroNat (unsafeCoerce Refl)
isZeroNat (NatRepr _) = NonZeroNat (unsafeCoerce Refl)

-- | Decrement a @NatRepr@
decNat :: NatRepr (n+1) -> NatRepr n
decNat (NatRepr i) = NatRepr (i-1)

-- | Increment a @NatRepr@
incNat :: NatRepr n -> NatRepr (n+1)
incNat (NatRepr x) | x == maxBound = error "incNat overflowed"
                   | otherwise = NatRepr (x+1)

halfNat :: NatRepr (n+n) -> NatRepr n
halfNat (NatRepr x) = NatRepr (x `div` 2)

addNat :: NatRepr m -> NatRepr n -> NatRepr (m+n)
addNat (NatRepr m) (NatRepr n) = NatRepr (m+n)

------------------------------------------------------------------------
-- SomeNat

someNat :: Integer -> Maybe (Some NatRepr)
someNat n | 0 <= n && n <= toInteger intMax = Just (Some (NatRepr (fromInteger n)))
          | otherwise = Nothing

-- | Return the maximum of two nat representations.
maxNat :: NatRepr m -> NatRepr n -> Some NatRepr
maxNat x y
  | widthVal x >= widthVal y = Some x
  | otherwise = Some y

------------------------------------------------------------------------
-- LeqProof

-- | @LeqProof m n@ is a type whose values are only inhabited when @m@
-- is less than or equal to @n@.
data LeqProof m n where
  LeqProof :: (m <= n) => LeqProof m n

-- | Return a LeqProof from compile time information.
knownLeq :: (m <= n, KnownNat m, KnownNat n) => LeqProof m n
knownLeq = LeqProof

testLeq :: NatRepr n -> NatRepr m -> Maybe (LeqProof n m)
testLeq (NatRepr n) (NatRepr m)
   | n <= m    = Just (unsafeCoerce (LeqProof :: LeqProof 0 0))
   | otherwise = Nothing