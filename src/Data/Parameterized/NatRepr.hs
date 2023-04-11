{-|
Description : Type level natural number representation at runtime
Copyright   : (c) Galois, Inc 2014-2019
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This defines a type 'NatRepr' for representing a type-level natural
at runtime.  This can be used to branch on a type-level value.  For
each @n@, @NatRepr n@ contains a single value containing the value
@n@.  This can be used to help use type-level variables on code
with data dependendent types.

The @TestEquality@ and @DecidableEq@ instances for 'NatRepr'
are implemented using 'unsafeCoerce', as is the `isZeroNat` function. This
should be typesafe because we maintain the invariant that the integer value
contained in a NatRepr value matches its static type.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
module Data.Parameterized.NatRepr
  ( NatRepr
  , natValue
  , intValue
  , knownNat
  , withKnownNat
  , IsZeroNat(..)
  , isZeroNat
  , isZeroOrGT1
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
  , mkNatRepr
  , maxNat
  , natRec
  , natRecStrong
  , natRecBounded
  , natRecStrictlyBounded
  , natForEach
  , natFromZero
  , NatCases(..)
  , testNatCases
    -- * Strict order
  , lessThanIrreflexive
  , lessThanAsymmetric
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
  , decideLeq
  , testLeq
  , testStrictLeq
  , leqRefl
  , leqSucc
  , leqTrans
  , leqZero
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
  , plusAssoc
  , mulComm
  , plusMinusCancel
  , minusPlusCancel
  , addMulDistribRight
  , withAddMulDistribRight
  , withSubMulDistribRight
  , mulCancelR
  , mul2Plus
  , lemmaMul
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

import Data.Bits ((.&.), bit)
import Data.Data
import Data.Type.Equality as Equality
import Data.Void as Void
import Numeric.Natural
import GHC.TypeNats ( KnownNat, Nat, SomeNat(..)
                    , type (+), type (-), type (*), type (<=)
                    , someNatVal )
import Unsafe.Coerce

import Data.Parameterized.Axiom
import Data.Parameterized.NatRepr.Internal
import Data.Parameterized.Some

maxInt :: Natural
maxInt = fromIntegral (maxBound :: Int)

intValue :: NatRepr n -> Integer
intValue n = toInteger (natValue n)
{-# INLINE intValue #-}

-- | Return the value of the nat representation.
widthVal :: NatRepr n -> Int
widthVal (NatRepr i) | i <= maxInt = fromIntegral i
                     | otherwise   = error ("Width is too large: " ++ show i)

withKnownNat :: forall n r. NatRepr n -> (KnownNat n => r) -> r
withKnownNat (NatRepr nVal) v =
  case someNatVal nVal of
    SomeNat (Proxy :: Proxy n') ->
      case unsafeAxiom :: n :~: n' of
        Refl -> v

data IsZeroNat n where
  ZeroNat    :: IsZeroNat 0
  NonZeroNat :: IsZeroNat (n+1)

isZeroNat :: NatRepr n -> IsZeroNat n
isZeroNat (NatRepr 0) = unsafeCoerce ZeroNat
isZeroNat (NatRepr _) = unsafeCoerce NonZeroNat

-- | Every nat is either zero or >= 1.
isZeroOrGT1 :: NatRepr n -> Either (n :~: 0) (LeqProof 1 n)
isZeroOrGT1 n =
  case isZeroNat n of
    ZeroNat    -> Left Refl
    NonZeroNat -> Right $
      -- We have n = m + 1 for some m.
      let
        -- | x <= x + 1
        leqPlus :: forall f x y. ((x + 1) ~ y) => f x ->  LeqProof 1 y
        leqPlus fx =
          case (plusComm fx (knownNat @1) :: x + 1 :~: 1 + x)    of { Refl ->
          case (plusMinusCancel (knownNat @1) fx :: 1+x-x :~: 1) of { Refl ->
          case (LeqProof :: LeqProof (x+1) y)                    of { LeqProof ->
          case (LeqProof :: LeqProof (1+x-x) (y-x))              of { LeqProof ->
            leqTrans (LeqProof :: LeqProof 1 (y-x))
                     (leqSub (LeqProof :: LeqProof y y)
                             (leqTrans (leqSucc (Proxy :: Proxy x))
                                       (LeqProof) :: LeqProof x y) :: LeqProof (y - x) y)
          }}}}
      in leqPlus (predNat n)

-- | Decrement a @NatRepr@
decNat :: (1 <= n) => NatRepr n -> NatRepr (n-1)
decNat (NatRepr i) = NatRepr (i-1)

-- | Get the predecessor of a nat
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
       -> case unsafeAxiom of
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
maxUnsigned w = bit (widthVal w) - 1

-- | Return minimum value for bitvector in two's complement with given width.
minSigned :: (1 <= w) => NatRepr w -> Integer
minSigned w = negate (bit (widthVal w - 1))

-- | Return maximum value for bitvector in two's complement with given width.
maxSigned :: (1 <= w) => NatRepr w -> Integer
maxSigned w = bit (widthVal w - 1) - 1

-- | @toUnsigned w i@ maps @i@ to a @i `mod` 2^w@.
toUnsigned :: NatRepr w -> Integer -> Integer
toUnsigned w i = maxUnsigned w .&. i

-- | @toSigned w i@ interprets the least-significant @w@ bits in @i@ as a
-- signed number in two's complement notation and returns that value.
toSigned :: (1 <= w) => NatRepr w -> Integer -> Integer
toSigned w i0
    | i > maxSigned w = i - bit (widthVal w)
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

-- | Turn an @Integral@ value into a @NatRepr@.  Returns @Nothing@
--   if the given value is negative.
someNat :: Integral a => a -> Maybe (Some NatRepr)
someNat x | x >= 0 = Just . Some . NatRepr $! fromIntegral x
someNat _ = Nothing

-- | Turn a @Natural@ into the corresponding @NatRepr@
mkNatRepr :: Natural -> Some NatRepr
mkNatRepr n = Some (NatRepr n)

-- | Return the maximum of two nat representations.
maxNat :: NatRepr m -> NatRepr n -> Some NatRepr
maxNat x y
  | natValue x >= natValue y = Some x
  | otherwise = Some y

------------------------------------------------------------------------
-- Arithmetic

-- | Produce evidence that @+@ is commutative.
plusComm :: forall f m g n . f m -> g n -> m+n :~: n+m
plusComm _ _ = unsafeAxiom

-- | Produce evidence that @+@ is associative.
plusAssoc :: forall f m g n h o . f m -> g n -> h o -> m+(n+o) :~: (m+n)+o
plusAssoc _ _ _ = unsafeAxiom

-- | Produce evidence that @*@ is commutative.
mulComm :: forall f m g n. f m -> g n -> (m * n) :~: (n * m)
mulComm _ _ = unsafeAxiom

mul2Plus :: forall f n. f n -> (n + n) :~: (2 * n)
mul2Plus n = case addMulDistribRight (Proxy @1) (Proxy @1) n of
               Refl -> Refl

-- | Cancel an add followed by a subtract
plusMinusCancel :: forall f m g n . f m -> g n -> (m + n) - n :~: m
plusMinusCancel _ _ = unsafeAxiom

minusPlusCancel :: forall f m g n . (n <= m) => f m -> g n -> (m - n) + n :~: m
minusPlusCancel _ _ = unsafeAxiom

addMulDistribRight :: forall n m p f g h. f n -> g m -> h p
                    -> ((n * p) + (m * p)) :~: ((n + m) * p)
addMulDistribRight _n _m _p = unsafeAxiom



withAddMulDistribRight :: forall n m p f g h a. f n -> g m -> h p
                    -> ( (((n * p) + (m * p)) ~ ((n + m) * p)) => a) -> a
withAddMulDistribRight n m p f =
  case addMulDistribRight n m p of
    Refl -> f

withSubMulDistribRight :: forall n m p f g h a. (m <= n) => f n -> g m -> h p
                    -> ( (((n * p) - (m * p)) ~ ((n - m) * p)) => a) -> a
withSubMulDistribRight _n _m _p f =
  case unsafeAxiom of
    (Refl :: (((n * p) - (m * p)) :~: ((n - m) * p)) ) -> f

------------------------------------------------------------------------
-- LeqProof

-- | @LeqProof m n@ is a type whose values are only inhabited when @m@
-- is less than or equal to @n@.
data LeqProof (m :: Nat) (n :: Nat) where
  LeqProof :: (m <= n) => LeqProof m n

-- | (<=) is a decidable relation on nats.
decideLeq :: NatRepr a -> NatRepr b -> Either (LeqProof a b) ((LeqProof a b) -> Void)
decideLeq (NatRepr m) (NatRepr n)
  | m <= n    = Left $ unsafeCoerce (LeqProof :: LeqProof 0 0)
  | otherwise = Right $
      \x -> seq x $ error "Impossible [decidable <= on NatRepr]"

testStrictLeq :: forall m n
               . (m <= n)
              => NatRepr m
              -> NatRepr n
              -> Either (LeqProof (m+1) n) (m :~: n)
testStrictLeq (NatRepr m) (NatRepr n)
  | m < n = Left (unsafeCoerce (LeqProof :: LeqProof 0 0))
  | otherwise = Right unsafeAxiom
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

-- | The strict order (\<), defined by n \< m \<-> n + 1 \<= m, is irreflexive.
lessThanIrreflexive :: forall f (a :: Nat). f a -> LeqProof (1 + a) a -> Void
lessThanIrreflexive a prf =
  let prf1 :: LeqProof (1 + a - a) (a - a)
      prf1 = leqSub2 prf (LeqProof :: LeqProof a a)
      prf2 :: 1 + a - a :~: 1
      prf2 = plusMinusCancel (knownNat @1) a
      prf3 :: a - a :~: 0
      prf3 = plusMinusCancel (knownNat @0) a
      prf4 :: LeqProof 1 0
      prf4 = case prf2 of Refl -> case prf3 of { Refl -> prf1 }
  in case prf4 of {}

-- | The strict order on the naturals is asymmetric
lessThanAsymmetric :: forall m f n
                    . LeqProof (n+1) m
                   -> LeqProof (m+1) n
                   -> f n
                   -> Void
lessThanAsymmetric nLTm mLTn n =
  case plusComm n (knownNat @1) :: n + 1 :~: 1 + n of { Refl ->
  case leqAdd (LeqProof :: LeqProof m m) (knownNat @1) :: LeqProof m (m+1) of
    LeqProof -> lessThanIrreflexive n $ leqTrans (leqTrans nLTm LeqProof) mLTn
  }

-- | @x `testLeq` y@ checks whether @x@ is less than or equal to @y@.
testLeq :: forall m n . NatRepr m -> NatRepr n -> Maybe (LeqProof m n)
testLeq (NatRepr m) (NatRepr n)
   | m <= n    = Just (unsafeCoerce (LeqProof :: LeqProof 0 0))
   | otherwise = Nothing
{-# NOINLINE testLeq #-}

-- | Apply reflexivity to LeqProof
leqRefl :: forall f n . f n -> LeqProof n n
leqRefl _ = LeqProof

leqSucc :: forall f z. f z -> LeqProof z (z + 1)
leqSucc fz = leqAdd (leqRefl fz :: LeqProof z z) (knownNat @1)

-- | Apply transitivity to LeqProof
leqTrans :: LeqProof m n -> LeqProof n p -> LeqProof m p
leqTrans LeqProof LeqProof = unsafeCoerce (LeqProof :: LeqProof 0 0)
{-# NOINLINE leqTrans #-}

-- | Zero is less than or equal to any 'Nat'.
leqZero :: LeqProof 0 n
leqZero = unsafeCoerce (LeqProof :: LeqProof 0 0)

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
leqAdd x _ = leqAdd2 x (leqZero @p)

leqAddPos :: (1 <= m, 1 <= n) => p m -> q n -> LeqProof 1 (m + n)
leqAddPos m n = leqAdd (leqProof (Proxy :: Proxy 1) m) n

-- | Produce proof that subtracting a value from the smaller element is smaller.
leqSub :: forall m n p . LeqProof m n -> LeqProof p m -> LeqProof (m-p) n
leqSub x _ = leqSub2 x (leqZero @p)

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

-- | Apply a function to each element in a range starting at zero;
-- return the list of values obtained.
natFromZero :: forall h a
            . NatRepr h
           -> (forall n. (n <= h) => NatRepr n -> a)
           -> [a]
natFromZero h f = natForEach (knownNat @0) h f

-- | Recursor for natural numbeers.
natRec :: forall p f
       .  NatRepr p
       -> f 0 {- ^ base case -}
       -> (forall n. NatRepr n -> f n -> f (n + 1))
       -> f p
natRec n base ind =
  case isZeroNat n of
    ZeroNat    -> base
    NonZeroNat -> let n' = predNat n
                  in ind n' (natRec n' base ind)

-- | Strong induction variant of the recursor.
natRecStrong :: forall p f
             .  NatRepr p
             -> f 0 {- ^ base case -}
             -> (forall n.
                  NatRepr n ->
                  (forall m. (m <= n) => NatRepr m -> f m) ->
                  f (n + 1)) {- ^ inductive step -}
             -> f p
natRecStrong p base ind = natRecStrong' base ind p
  where -- We can't use use "flip" or some other basic combinator
        -- because type variables can't be instantiated to contain "forall"s.
        natRecStrong' :: forall p' f'
                      .  f' 0 {- ^ base case -}
                      -> (forall n.
                            NatRepr n ->
                            (forall m. (m <= n) => NatRepr m -> f' m) ->
                            f' (n + 1)) {- ^ inductive step -}
                      -> NatRepr p'
                      -> f' p'
        natRecStrong' base' ind' n =
          case isZeroNat n of
            ZeroNat    -> base'
            NonZeroNat -> ind' (predNat n) (natRecStrong' base' ind')

-- | Bounded recursor for natural numbers.
--
-- If you can prove:
-- - Base case: f 0
-- - Inductive step: if n <= h and (f n) then (f (n + 1))
-- You can conclude: for all n <= h, (f (n + 1)).
natRecBounded :: forall m h f. (m <= h)
              => NatRepr m
              -> NatRepr h
              -> f 0
              -> (forall n. (n <= h) => NatRepr n -> f n -> f (n + 1))
              -> f (m + 1)
natRecBounded m h base indH =
  case isZeroOrGT1 m of
    Left Refl      -> indH (knownNat @0) base
    Right LeqProof ->
      case decideLeq m h of
        Left LeqProof {- :: m <= h -} ->
          let -- Since m is non-zero, it is n + 1 for some n.
              lemma :: LeqProof (m-1) h
              lemma = leqSub (LeqProof :: LeqProof m h) (LeqProof :: LeqProof 1 m)
          in indH m $
            case lemma of { LeqProof ->
            case minusPlusCancel m (knownNat @1) of { Refl ->
              natRecBounded @(m - 1) @h @f (predNat m) h base indH
            }}
        Right f {- :: (m <= h) -> Void -} ->
          absurd $ f (LeqProof :: LeqProof m h)

-- | A version of 'natRecBounded' which doesn't require the type index of the
-- result to be greater than @0@ and provides a strict inequality constraint.
natRecStrictlyBounded ::
  forall m f.
  NatRepr m ->
  f 0 ->
  (forall n. (n + 1 <= m) => NatRepr n -> f n -> f (n + 1)) ->
  f m
natRecStrictlyBounded m base indH =
  case isZeroNat m of
    ZeroNat -> base
    NonZeroNat ->
      case predNat m of
        (p :: NatRepr p) ->
          natRecBounded
            p
            p
            base
            (\(k :: NatRepr n) (v :: f n) ->
              case leqAdd2 (LeqProof :: LeqProof n p) (LeqProof :: LeqProof 1 1) of
                LeqProof -> indH k v)

mulCancelR ::
  (1 <= c, (n1 * c) ~ (n2 * c)) => f1 n1 -> f2 n2 -> f3 c -> (n1 :~: n2)
mulCancelR _ _ _ = unsafeAxiom

-- | Used in @Vector@
lemmaMul :: (1 <= n) => p w -> q n -> (w + (n-1) * w) :~: (n * w)
lemmaMul _ _ = unsafeAxiom
