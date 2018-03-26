{-|
Copyright        : (c) Galois, Inc 2014-2015
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines a type 'NatRepr' for representing a type-level natural
at runtime.  This can be used to branch on a type-level value.  For
each @n@, @NatRepr n@ contains a single value containing the vlaue
@n@.  This can be used to help use type-level variables on code
with data dependendent types.

The 'TestEquality' instance for 'NatRepr' is implemented using
'unsafeCoerce', as is the `isZeroNat` function. This should be
typesafe because we maintain the invariant that the integer value
contained in a NatRepr value matches its static type.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Trustworthy #-}
#if MIN_VERSION_base(4,9,0)
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#endif
module Data.Parameterized.NatRepr
  ( NatRepr
  , natValue
  , knownNat
  , withKnownNat
  , IsZeroNat(..)
  , isZeroNat
  , NatComparison(..)
  , compareNat
  , decNat
  , predNat
  , incNat
  , addNat
  , subNat
  , divNat
  , halfNat
  , withDivModNat
  , natMultiply
  , someNat
  , maxNat
  , natRec
  , natForEach
  , NatCases(..)
  , testNatCases
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
  , testStrictLeq
  , leqRefl
  , leqTrans
  , leqAdd2
  , leqSub2
  , leqMulCongr
    -- * LeqProof combinators
  , leqProof
  , withLeqProof
  , isPosNat
  , leqAdd
  , leqSub
  , leqMulPos
  , leqAddPos
  , addIsLeq
  , withAddLeq
  , addPrefixIsLeq
  , withAddPrefixLeq
  , addIsLeqLeft1
  , dblPosIsPos
  , leqMulMono
    -- * Arithmetic proof
  , plusComm
  , plusMinusCancel
  , minusPlusCancel
  , withAddMulDistribRight
  , withSubMulDistribRight
  , mulCancelR
    -- * Re-exports typelists basics
--  , NatK
  , type (+)
  , type (-)
  , type (*)
  , type (<=)
  , Equality.TestEquality(..)
  , (Equality.:~:)(..)
  , Data.Parameterized.Some.Some
  ) where

import Data.Bits ((.&.))
import Data.Hashable
import Data.Proxy as Proxy
import Data.Type.Equality as Equality
import GHC.TypeLits as TypeLits
import Unsafe.Coerce

import Data.Parameterized.Classes
import Data.Parameterized.Some

maxInt :: Integer
maxInt = toInteger (maxBound :: Int)

------------------------------------------------------------------------
-- Nat

-- | A runtime presentation of a type-level 'Nat'.
--
-- This can be used for performing dynamic checks on a type-level natural
-- numbers.
newtype NatRepr (n::Nat) = NatRepr { natValue :: Integer
                                     -- ^ The underlying integer value of the number.
                                   }
  deriving (Hashable)

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

instance ShowF NatRepr

instance HashableF NatRepr where
  hashWithSaltF = hashWithSalt

-- | This generates a NatRepr from a type-level context.
knownNat :: forall n . KnownNat n => NatRepr n
knownNat = NatRepr (natVal (Proxy :: Proxy n))

instance (KnownNat n) => KnownRepr NatRepr n where
  knownRepr = knownNat

{-# DEPRECATED withKnownNat "This function is potentially unsafe and is schedueled to be removed." #-}
withKnownNat :: forall n r. NatRepr n -> (KnownNat n => r) -> r
withKnownNat (NatRepr nVal) v =
  case someNatVal nVal of
    Just (SomeNat (Proxy :: Proxy n')) ->
      case unsafeCoerce (Refl :: 0 :~: 0) :: n :~: n' of
        Refl -> v
    Nothing -> error "withKnownNat: inner value in NatRepr is not a natural"

data IsZeroNat n where
  ZeroNat    :: IsZeroNat 0
  NonZeroNat :: IsZeroNat (n+1)

isZeroNat :: NatRepr n -> IsZeroNat n
isZeroNat (NatRepr 0) = unsafeCoerce ZeroNat
isZeroNat (NatRepr _) = unsafeCoerce NonZeroNat

-- | Decrement a @NatRepr@
decNat :: (1 <= n) => NatRepr n -> NatRepr (n-1)
decNat (NatRepr i) = NatRepr (i-1)

-- | Get the predicessor of a nat
predNat :: NatRepr (n+1) -> NatRepr n
predNat (NatRepr i) = NatRepr (i-1)

-- | Increment a @NatRepr@
incNat :: NatRepr n -> NatRepr (n+1)
incNat (NatRepr x) = NatRepr (x+1)

halfNat :: NatRepr (n+n) -> NatRepr n
halfNat (NatRepr x) = NatRepr (x `div` 2)

addNat :: NatRepr m -> NatRepr n -> NatRepr (m+n)
addNat (NatRepr m) (NatRepr n) = NatRepr (m+n)

subNat :: (n <= m) => NatRepr m -> NatRepr n -> NatRepr (m-n)
subNat (NatRepr m) (NatRepr n) = NatRepr (m-n)

divNat :: (1 <= n) => NatRepr (m * n) -> NatRepr n -> NatRepr m
divNat (NatRepr x) (NatRepr y) = NatRepr (div x y)

withDivModNat :: forall n m a.
                 NatRepr n
              -> NatRepr m
              -> (forall div mod. (n ~ ((div * m) + mod)) =>
                  NatRepr div -> NatRepr mod -> a)
              -> a
withDivModNat n m f =
  case ( Some (NatRepr divPart), Some (NatRepr modPart)) of
     ( Some (divn :: NatRepr div), Some (modn :: NatRepr mod) )
       -> case unsafeCoerce (Refl :: 0 :~: 0) of
            (Refl :: (n :~: ((div * m) + mod))) -> f divn modn
  where
    (divPart, modPart) = divMod (natValue n) (natValue m)

natMultiply :: NatRepr n -> NatRepr m -> NatRepr (n * m)
natMultiply (NatRepr n) (NatRepr m) = NatRepr (n * m)

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
minSigned w = negate (2^(natValue w - 1))

-- | Return maximum value for bitvector in 2s complement with given width.
maxSigned :: (1 <= w) => NatRepr w -> Integer
maxSigned w = 2^(natValue w - 1) - 1

-- | @toUnsigned w i@ maps @i@ to a @i `mod` 2^w@.
toUnsigned :: NatRepr w -> Integer -> Integer
toUnsigned w i = maxUnsigned w .&. i

-- | @toSigned w i@ interprets the least-significant @w@ bits in @i@ as a
-- signed number in two's complement notation and returns that value.
toSigned :: (1 <= w) => NatRepr w -> Integer -> Integer
toSigned w i0
    | i > maxSigned w = i - 2^(natValue w)
    | otherwise       = i
  where i = i0 .&. maxUnsigned w

-- | @unsignedClamp w i@ rounds @i@ to the nearest value between
-- @0@ and @2^w-1@ (inclusive).
unsignedClamp :: NatRepr w -> Integer -> Integer
unsignedClamp w i
  | i < minUnsigned w = minUnsigned w
  | i > maxUnsigned w = maxUnsigned w
  | otherwise         = i

-- | @signedClamp w i@ rounds @i@ to the nearest value between
-- @-2^(w-1)@ and @2^(w-1)-1@ (inclusive).
signedClamp :: (1 <= w) => NatRepr w -> Integer -> Integer
signedClamp w i
  | i < minSigned w = minSigned w
  | i > maxSigned w = maxSigned w
  | otherwise       = i

------------------------------------------------------------------------
-- Some NatRepr

someNat :: Integer -> Maybe (Some NatRepr)
someNat n | 0 <= n && n <= toInteger maxInt = Just (Some (NatRepr (fromInteger n)))
          | otherwise = Nothing

-- | Return the maximum of two nat representations.
maxNat :: NatRepr m -> NatRepr n -> Some NatRepr
maxNat x y
  | natValue x >= natValue y = Some x
  | otherwise = Some y

------------------------------------------------------------------------
-- Arithmetic

-- | Produce evidence that + is commutative.
plusComm :: forall f m g n . f m -> g n -> m+n :~: n+m
plusComm _ _ = unsafeCoerce (Refl :: m+n :~: m+n)

-- | Cancel an add followed b a subtract
plusMinusCancel :: forall f m g n . f m -> g n -> (m + n) - n :~: m
plusMinusCancel _ _ = unsafeCoerce (Refl :: m :~: m)

minusPlusCancel :: forall f m g n . (n <= m) => f m -> g n -> (m - n) + n :~: m
minusPlusCancel _ _ = unsafeCoerce (Refl :: m :~: m)

withAddMulDistribRight :: forall n m p f g h a. f n -> g m -> h p
                    -> ( (((n * p) + (m * p)) ~ ((n + m) * p)) => a) -> a
withAddMulDistribRight _n _m _p f =
  case unsafeCoerce (Refl :: 0 :~: 0) of
    (Refl :: (((n * p) + (m * p)) :~: ((n + m) * p)) ) -> f

withSubMulDistribRight :: forall n m p f g h a. (m <= n) => f n -> g m -> h p
                    -> ( (((n * p) - (m * p)) ~ ((n - m) * p)) => a) -> a
withSubMulDistribRight _n _m _p f =
  case unsafeCoerce (Refl :: 0 :~: 0) of
    (Refl :: (((n * p) - (m * p)) :~: ((n - m) * p)) ) -> f



------------------------------------------------------------------------
-- LeqProof

-- | @LeqProof m n@ is a type whose values are only inhabited when @m@
-- is less than or equal to @n@.
data LeqProof m n where
  LeqProof :: (m <= n) => LeqProof m n

testStrictLeq :: forall m n
               . (m <= n)
              => NatRepr m
              -> NatRepr n
              -> Either (LeqProof (m+1) n) (m :~: n)
testStrictLeq (NatRepr m) (NatRepr n)
  | m < n = Left (unsafeCoerce (LeqProof :: LeqProof 0 0))
  | otherwise = Right (unsafeCoerce (Refl :: m :~: m))
{-# NOINLINE testStrictLeq #-}

-- As for NatComparison above, but works with LeqProof
data NatCases m n where
  -- First number is less than second.
  NatCaseLT :: LeqProof (m+1) n -> NatCases m n
  NatCaseEQ :: NatCases m m
  -- First number is greater than second.
  NatCaseGT :: LeqProof (n+1) m -> NatCases m n

testNatCases ::  forall m n
              . NatRepr m
             -> NatRepr n
             -> NatCases m n
testNatCases m n =
  case compare (natValue m) (natValue n) of
    LT -> NatCaseLT (unsafeCoerce (LeqProof :: LeqProof 0 0))
    EQ -> unsafeCoerce $ (NatCaseEQ :: NatCases m m)
    GT -> NatCaseGT (unsafeCoerce (LeqProof :: LeqProof 0 0))
{-# NOINLINE testNatCases #-}

-- | @x `testLeq` y@ checks whether @x@ is less than or equal to @y@.
testLeq :: forall m n . NatRepr m -> NatRepr n -> Maybe (LeqProof m n)
testLeq (NatRepr m) (NatRepr n)
   | m <= n    = Just (unsafeCoerce (LeqProof :: LeqProof 0 0))
   | otherwise = Nothing
{-# NOINLINE testLeq #-}

-- | Apply reflexivity to LeqProof
leqRefl :: forall f n . f n -> LeqProof n n
leqRefl _ = LeqProof


-- | Apply transitivity to LeqProof
leqTrans :: LeqProof m n -> LeqProof n p -> LeqProof m p
leqTrans LeqProof LeqProof = unsafeCoerce (LeqProof :: LeqProof 0 0)
{-# NOINLINE leqTrans #-}

-- | Add both sides of two inequalities
leqAdd2 :: LeqProof x_l x_h -> LeqProof y_l y_h -> LeqProof (x_l + y_l) (x_h + y_h)
leqAdd2 x y = seq x $ seq y $ unsafeCoerce (LeqProof :: LeqProof 0 0)
{-# NOINLINE leqAdd2 #-}

-- | Subtract sides of two inequalities.
leqSub2 :: LeqProof x_l x_h
        -> LeqProof y_l y_h
        -> LeqProof (x_l-y_h) (x_h-y_l)
leqSub2 LeqProof LeqProof = unsafeCoerce (LeqProof :: LeqProof 0 0)
{-# NOINLINE leqSub2 #-}

------------------------------------------------------------------------
-- LeqProof combinators

-- | Create a leqProof using two proxies
leqProof :: (m <= n) => f m -> g n -> LeqProof m n
leqProof _ _ = LeqProof

withLeqProof :: LeqProof m n -> ((m <= n) => a) -> a
withLeqProof p a =
  case p of
    LeqProof -> a

-- | Test whether natural number is positive.
isPosNat :: NatRepr n -> Maybe (LeqProof 1 n)
isPosNat = testLeq (knownNat :: NatRepr 1)

-- | Congruence rule for multiplication
leqMulCongr :: LeqProof a x
            -> LeqProof b y
            -> LeqProof (a*b) (x*y)
leqMulCongr LeqProof LeqProof = unsafeCoerce (LeqProof :: LeqProof 1 1)
{-# NOINLINE leqMulCongr #-}

-- | Multiplying two positive numbers results in a positive number.
leqMulPos :: forall p q x y
          .  (1 <= x, 1 <= y)
          => p x
          -> q y
          -> LeqProof 1 (x*y)
leqMulPos _ _ = leqMulCongr (LeqProof :: LeqProof 1 x) (LeqProof :: LeqProof 1 y)

leqMulMono :: (1 <= x) => p x -> q y -> LeqProof y (x * y)
leqMulMono x y = leqMulCongr (leqProof (Proxy :: Proxy 1) x) (leqRefl y)

-- | Produce proof that adding a value to the larger element in an LeqProof
-- is larger
leqAdd :: forall f m n p . LeqProof m n -> f p -> LeqProof m (n+p)
leqAdd x _ = leqAdd2 x (LeqProof :: LeqProof 0 p)

leqAddPos :: (1 <= m, 1 <= n) => p m -> q n -> LeqProof 1 (m + n)
leqAddPos m n = leqAdd (leqProof (Proxy :: Proxy 1) m) n

-- | Produce proof that subtracting a value from the smaller element is smaller.
leqSub :: forall m n p . LeqProof m n -> LeqProof p m -> LeqProof (m-p) n
leqSub x _ = leqSub2 x (LeqProof :: LeqProof 0 p)

addIsLeq :: f n -> g m -> LeqProof n (n + m)
addIsLeq n m = leqAdd (leqRefl n) m

addPrefixIsLeq :: f m -> g n -> LeqProof n (m + n)
addPrefixIsLeq m n =
  case plusComm n m of
    Refl -> addIsLeq n m

dblPosIsPos :: forall n . LeqProof 1 n -> LeqProof 1 (n+n)
dblPosIsPos x = leqAdd x Proxy

addIsLeqLeft1 :: forall n n' m . LeqProof (n + n') m -> LeqProof n m
addIsLeqLeft1 p =
    case plusMinusCancel n n' of
      Refl -> leqSub p le
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

natForEach' :: forall l h a
            . NatRepr l
            -> NatRepr h
            -> (forall n. LeqProof l n -> LeqProof n h -> NatRepr n -> a)
            -> [a]
natForEach' l h f
  | Just LeqProof  <- testLeq l h =
    let f' :: forall n. LeqProof (l + 1) n -> LeqProof n h -> NatRepr n -> a
        f' = \lp hp -> f (addIsLeqLeft1 lp) hp
     in f LeqProof LeqProof l : natForEach' (incNat l) h f'
  | otherwise             = []

-- | Apply a function to each element in a range; return the list of values
-- obtained.
natForEach :: forall l h a
            . NatRepr l
           -> NatRepr h
           -> (forall n. (l <= n, n <= h) => NatRepr n -> a)
           -> [a]
natForEach l h f = natForEach' l h (\LeqProof LeqProof -> f)

-- | Recursor for natural numbeers.
natRec :: forall m f
       .  NatRepr m
       -> f 0
       -> (forall n. NatRepr n -> f n -> f (n + 1))
       -> f m
natRec n f0 ih = go n
  where
    go :: forall n'. NatRepr n' -> f n'
    go n' = case isZeroNat n' of
              ZeroNat    -> f0
              NonZeroNat -> let n'' = predNat n' in ih n'' (go n'')

mulCancelR ::
  (1 <= c, (n1 * c) ~ (n2 * c)) => f1 n1 -> f2 n2 -> f3 c -> (n1 :~: n2)
mulCancelR _ _ _ = unsafeCoerce Refl
