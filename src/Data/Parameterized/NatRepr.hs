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
{-# LANGUAGE PatternGuards #-}

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
  , subNat
  , halfNat
  , someNat
  , maxNat
  , natForEach
    -- * Bitvector utilities
  , widthVal
  , minUnsigned
  , maxUnsigned
  , minSigned
  , maxSigned
  , toUnsigned
  , toSigned
  , unsignedClamp
  , signedClamp
    -- * LeqProof
  , LeqProof(..)
  , testLeq
  , leqRefl
  , leqTrans
  , leqCong1
  , leqCong2
  , leqAdd
  , leqSub
    -- * LeqProof combinators
  , leqProof
  , withLeqProof
  , isPosNat
  , addIsLeq
  , withAddLeq
  , addPrefixIsLeq
  , withAddPrefixLeq
  , addIsLeqLeft1
  , dblPosIsPos
    -- * Arithmetic proof
  , plusComm
  , plusMinusCancel
    -- * Re-exports typelists basics
  , NatK
  , type (+)
  , type (-)
  , type (*)
  , type (<=)
  , Equality.TestEquality(..)
  , (Equality.:~:)(..)
  , Data.Parameterized.Some.Some
  ) where

import Control.Exception (assert)
import Data.Bits ((.&.))
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
decNat :: (1 <= n) => NatRepr n -> NatRepr n
decNat (NatRepr i) = NatRepr (i-1)

-- | Increment a @NatRepr@
incNat :: NatRepr n -> NatRepr (n+1)
incNat (NatRepr x) = NatRepr (x+1)

halfNat :: NatRepr (n+n) -> NatRepr n
halfNat (NatRepr x) = NatRepr (x `div` 2)

addNat :: NatRepr m -> NatRepr n -> NatRepr (m+n)
addNat (NatRepr m) (NatRepr n) = NatRepr (m+n)

subNat :: (n <= m) => NatRepr m -> NatRepr n -> NatRepr (m-n)
subNat (NatRepr m) (NatRepr n) = NatRepr (m-n)

------------------------------------------------------------------------
-- Operations for using NatRepr as a bitwidth.

-- | Return minimum unsigned value for bitvector with given width (always 0).
minUnsigned :: NatRepr w -> Integer
minUnsigned _ = 0

-- | Return maximum unsigned value for bitvector with given width.
maxUnsigned :: NatRepr w -> Integer
maxUnsigned w = 2^(natValue w) - 1

-- | Return minimum value for bitvector in 2s complement with given width.
minSigned :: (1 <= w) => NatRepr w -> Integer
minSigned w = - 2^(natValue w - 1)

-- | Return maximum value for bitvector in 2s complement with given width.
maxSigned :: (1 <= w) => NatRepr w -> Integer
maxSigned w = 2^(natValue w - 1) - 1

-- | @toUnsigned w i@ maps @i@ to a @i `mod` 2^w@.
toUnsigned :: NatRepr w -> Integer -> Integer
toUnsigned w i = maxUnsigned w .&. i

-- | @toSigned w i@ interprets the least-significnt @w@ bits in @i@ as a
-- signed number in two's complement notation and returns that value.
toSigned :: (1 <= w) => NatRepr w -> Integer -> Integer
toSigned w i
  | i > maxSigned w = i - 2^(natValue w)
  | otherwise       = i

-- | @unsignedClamp w i@ rounds @i@ to the nearest value between
-- @0@ and @2^w-i@ (inclusive).
unsignedClamp :: NatRepr w -> Integer -> Integer
unsignedClamp w i
  | i < minUnsigned w = minUnsigned w
  | i > maxUnsigned w = maxUnsigned w
  | otherwise         = i

-- | @signedClamp w i@ rounds @i@ to the nearest value between
-- @-2^(w-1)@ and @2^(w-1)-i@ (inclusive).
signedClamp :: (1 <= w) => NatRepr w -> Integer -> Integer
signedClamp w i
  | i < minSigned w = minSigned w
  | i > maxSigned w = maxSigned w
  | otherwise       = i

------------------------------------------------------------------------
-- Some NatRepr

someNat :: Integer -> Maybe (Some NatRepr)
someNat n | 0 <= n && n <= toInteger intMax = Just (Some (NatRepr (fromInteger n)))
          | otherwise = Nothing

-- | Return the maximum of two nat representations.
maxNat :: NatRepr m -> NatRepr n -> Some NatRepr
maxNat x y
  | natValue x >= natValue y = Some x
  | otherwise = Some y

------------------------------------------------------------------------
-- Arithmetic

-- | Produce evidence that + is commutative.
plusComm :: f m -> g n -> m+n :~: n+m
plusComm _ _ = unsafeCoerce (Refl :: 0 :~: 0)

-- | Cancel an add followed b a subtract
plusMinusCancel :: f m -> g n -> (m + n) - n :~: m
plusMinusCancel _ _ = unsafeCoerce (Refl :: 0 :~: 0)

------------------------------------------------------------------------
-- LeqProof

-- | @LeqProof m n@ is a type whose values are only inhabited when @m@
-- is less than or equal to @n@.
data LeqProof m n where
  LeqProof :: (m <= n) => LeqProof m n

testLeq :: NatRepr n -> NatRepr m -> Maybe (LeqProof n m)
testLeq (NatRepr n) (NatRepr m)
   | n <= m    = Just (unsafeCoerce (LeqProof :: LeqProof 0 0))
   | otherwise = Nothing

-- | Apply reflexivity to LeqProof
leqRefl :: f n -> LeqProof n n
leqRefl _ = unsafeCoerce (LeqProof :: LeqProof 0 0)

-- | Apply transitivity to LeqProof
leqTrans :: LeqProof m n -> LeqProof n p -> LeqProof m p
leqTrans x y = seq x $ seq y $ unsafeCoerce (LeqProof :: LeqProof 0 0)

-- | Replace first argument in proof with equivalent type.
leqCong1 :: LeqProof m p -> m :~: n -> LeqProof n p
leqCong1 x y = seq x $ seq y $ unsafeCoerce (LeqProof :: LeqProof 0 0)

-- | Replace second argument in proof with equivalent type.
leqCong2 :: LeqProof p m  -> m :~: n -> LeqProof p n
leqCong2 x y = seq x $ seq y $ unsafeCoerce (LeqProof :: LeqProof 0 0)

-- | Produce proof that adding a value to the larger element in an LeqProof
-- is larger
leqAdd :: LeqProof m n -> f p -> LeqProof m (n+p)
leqAdd x _ = seq x $ unsafeCoerce (LeqProof :: LeqProof 0 0)

-- | Produce proof that subtracting a value from the smaller element is smaller.
leqSub :: LeqProof m n -> LeqProof p m -> LeqProof (m-p) n
leqSub x y = seq x $ seq y $ unsafeCoerce (LeqProof :: LeqProof 0 0)

------------------------------------------------------------------------
-- LeqProof combinators

-- | Create a leqProof using two proxies
leqProof :: (m <= n) => f m -> f n -> LeqProof m n
leqProof _ _ = LeqProof

withLeqProof :: LeqProof m n -> ((m <= n) => a) -> a
withLeqProof p a =
  case p of
    LeqProof -> a

-- | Test whether natural number is positive.
isPosNat :: NatRepr n -> Maybe (LeqProof 1 n)
isPosNat = testLeq (knownNat :: NatRepr 1)

addIsLeq :: f n -> g m -> LeqProof n (n + m)
addIsLeq n m = leqAdd (leqRefl n) m

addPrefixIsLeq :: f m -> g n -> LeqProof n (m + n)
addPrefixIsLeq m n = leqCong2 (addIsLeq n m) (plusComm n m)

dblPosIsPos :: forall n . LeqProof 1 n -> LeqProof 1 (n+n)
dblPosIsPos x = leqAdd x Proxy

addIsLeqLeft1 :: forall n n' m . LeqProof (n + n') m -> LeqProof n m
addIsLeqLeft1 p = leqCong1 (leqSub p le) (plusMinusCancel n n')
  where n :: Proxy n
        n = Proxy
        n' :: Proxy n'
        n' = Proxy
        le :: LeqProof n' (n + n')
        le = addPrefixIsLeq n n'

{-# INLINE withAddPrefixLeq #-}
withAddPrefixLeq :: NatRepr n -> NatRepr m -> ((m <= n + m) => a) -> a
withAddPrefixLeq n m = withLeqProof (addPrefixIsLeq n m)

withAddLeq :: forall n m a. NatRepr n -> NatRepr m -> ((n <= n + m) => NatRepr (n + m) -> a) -> a
withAddLeq n m f = withLeqProof (addIsLeq n m) (f (addNat n m))

natForEach' :: forall l h a. NatRepr l -> NatRepr h
              -> (forall n. LeqProof l n -> LeqProof n h -> NatRepr n -> a) -> [a]
natForEach' l h f
  | Just LeqProof  <- testLeq l h = let f' :: forall n. LeqProof (l + 1) n -> LeqProof n h -> NatRepr n -> a
                                        f' = \lp hp -> f (addIsLeqLeft1 lp) hp
                                    in
                                      f LeqProof LeqProof l : natForEach' (incNat l) h f'
  | otherwise             = []


natForEach :: forall l h a. NatRepr l -> NatRepr h
              -> (forall n. (l <= n, n <= h) => NatRepr n -> a) -> [a]
natForEach l h f = natForEach' l h (\LeqProof LeqProof -> f)
