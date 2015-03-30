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
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}

module Data.Parameterized.NatRepr
  ( NatRepr
  , natValue
  , knownNat
  , IsZeroNat(..)
  , isZeroNat
  , NatComparison(..)
  , compareNat

  , decNat
  , incNat
  , addNat
  , halfNat
  , someNat
  , maxNat
    -- * Bitvector utilities
  , widthVal
  , minUnsigned
  , maxUnsigned
  , minSigned
  , maxSigned

    -- * LeqProof
  , LeqProof(..)
  , knownLeq
  , testLeq
  , addIsLeq
  , withAddLeq
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

newtype NatRepr (n::Nat) = NatRepr { natValue :: Integer }
  deriving (Hashable)

maxInt :: Integer
maxInt = toInteger (maxBound :: Int)

-- | Return the value of the nat representation.
widthVal :: NatRepr n -> Int
widthVal (NatRepr i) | i < maxInt = fromInteger i
                     | otherwise = error "Width is too large."

instance Eq (NatRepr m) where
  _ == _ = True

instance TestEquality NatRepr where
  testEquality (NatRepr m) (NatRepr n)
    | m == n = Just (unsafeCoerce Refl)
    | otherwise = Nothing

-- | Result of comparing two numbers.
data NatComparison m n where
  -- First number is less than second.
  NatLT :: !(NatRepr y) -> NatComparison x (x+(y+1))
  NatEQ :: NatComparison x x
  -- First number is greater than second.
  NatGT :: !(NatRepr y) -> NatComparison (x+(y+1)) x

compareNat :: NatRepr m -> NatRepr n -> NatComparison m n
compareNat m n =
  case compare (natValue m) (natValue n) of
    LT -> unsafeCoerce $ NatLT (NatRepr (natValue n - natValue m - 1))
    EQ -> unsafeCoerce $ NatEQ
    GT -> unsafeCoerce $ NatGT (NatRepr (natValue m - natValue n - 1))

instance OrdF NatRepr where
  compareF x y =
    case compareNat x y of
      NatLT _ -> LTF
      NatEQ -> EQF
      NatGT _ -> GTF

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
  ZeroNat    :: IsZeroNat 0
  NonZeroNat :: IsZeroNat (n+1)

isZeroNat :: NatRepr n -> IsZeroNat n
isZeroNat (NatRepr 0) = unsafeCoerce ZeroNat
isZeroNat (NatRepr _) = unsafeCoerce NonZeroNat

-- | Decrement a @NatRepr@
decNat :: NatRepr (n+1) -> NatRepr n
decNat (NatRepr i) = NatRepr (i-1)

-- | Increment a @NatRepr@
incNat :: NatRepr n -> NatRepr (n+1)
incNat (NatRepr x) = NatRepr (x+1)

halfNat :: NatRepr (n+n) -> NatRepr n
halfNat (NatRepr x) = NatRepr (x `div` 2)

addNat :: NatRepr m -> NatRepr n -> NatRepr (m+n)
addNat (NatRepr m) (NatRepr n) = NatRepr (m+n)

------------------------------------------------------------------------
-- Operations for working with SomeNat

-- | Return minimum unsigned value for bitvector with given width (always 0).
minUnsigned :: NatRepr w -> Integer
minUnsigned _ = 0

-- | Return maximum unsigned value for bitvector with given width.
maxUnsigned :: NatRepr w -> Integer
maxUnsigned w = 2^(natValue w) - 1

-- | Return minimum value for bitvector in 2s complement with given width.
minSigned :: NatRepr (w+1) -> Integer
minSigned w = - 2^(natValue w - 1)

-- | Return maximum value for bitvector in 2s complement with given width.
maxSigned :: NatRepr (w+1) -> Integer
maxSigned w = 2^(natValue w - 1) - 1

------------------------------------------------------------------------
-- SomeNat

someNat :: Integer -> Maybe (Some NatRepr)
someNat n | 0 <= n && n <= toInteger intMax = Just (Some (NatRepr (fromInteger n)))
          | otherwise = Nothing

-- | Return the maximum of two nat representations.
maxNat :: NatRepr m -> NatRepr n -> Some NatRepr
maxNat x y
  | natValue x >= natValue y = Some x
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

addIsLeq :: forall n m. NatRepr n -> NatRepr m -> LeqProof n (n + m)
addIsLeq _ _ = unsafeCoerce (LeqProof :: LeqProof 0 0)

withAddLeq :: forall n m a. NatRepr n -> NatRepr m -> ((n <= n + m) => NatRepr (n + m) -> a) -> a
withAddLeq n m f = case addIsLeq n m of
                      LeqProof -> f (addNat n m)