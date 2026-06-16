{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{-|
Copyright        : (c) Galois, Inc 2021

@'Fin' n@ is a finite type with exactly @n@ elements. Essentially, they bundle a
'NatRepr' that has an existentially-quantified type parameter with a proof that
its parameter is less than some fixed natural.

They are useful in combination with types of a fixed size. For example 'Fin' is
used as the index in the 'Data.Functor.WithIndex.FunctorWithIndex' instance for
'Data.Parameterized.Vector'. As another example, a @Map ('Fin' n) a@ is a @Map@
that naturally has a fixed size bound of @n@.
-}
module Data.Parameterized.Fin
  ( Fin
  , mkFin
  , mkFinModN
  , buildFin
  , countFin
  , viewFin
  , finFromNatModN
  , finToNat
  , embed
  , tryEmbed
  , minFin
  , incFin
  , fin0Absurd
  , addFinModN
  , subFinModN
  , mulFinModN
  , negFinModN
  , recipFinModN
  ) where

import Data.Hashable (Hashable(..))
import GHC.TypeNats (KnownNat)
import Numeric.Natural (Natural)

import Data.Parameterized.NatRepr
import Data.Parameterized.Some (Some(..))

-- | The type @'Fin' n@ has exactly @n@ inhabitants.
data Fin n =
  -- GHC 8.6 and 8.4 require parentheses around 'i + 1 <= n'
  forall i. (i + 1 <= n) => Fin { _getFin :: NatRepr i }

instance Eq (Fin n) where
  i == j = finToNat i == finToNat j

instance Ord (Fin n) where
  compare i j = compare (finToNat i) (finToNat j)

instance Hashable (Fin n) where
  hashWithSalt salt (Fin i) = hashWithSalt salt i

instance (1 <= n, KnownNat n) => Bounded (Fin n) where
  minBound = Fin (knownNat @0)
  maxBound =
    case minusPlusCancel (knownNat @n) (knownNat @1) of
      Refl -> Fin (decNat (knownNat @n))

-- | Arithmetic is performed modulo @n@.
instance (1 <= n, KnownNat n) => Num (Fin n) where
  (+) = addFinModN (knownNat @n)
  (-) = subFinModN (knownNat @n)
  (*) = mulFinModN (knownNat @n)
  negate = negFinModN (knownNat @n)

  -- | We consider all Fin values to be non-negative. Therefore, this always
  -- returns the input unchanged.
  abs = id

  -- | We consider all Fin values to be non-negative. Therefore, this always
  -- returns either 'minFin' (i.e., zero) or @'mkFinModN' n (knownNat \@1)@
  -- (i.e., one). Note that in the degenerate case of @'Fin' 1@, these values
  -- will be equal to each other.
  signum f
    | f == minFin
    = f
    | otherwise
    = mkFinModN (knownNat @n) (knownNat @1)

  -- | Negative integers are negated, reduced modulo @n@, and then negated
  -- again using 'negFinModN'.
  fromInteger i
    | i >= 0
    = finFromNatModN n (fromInteger i)
    | otherwise
    = negFinModN n (finFromNatModN n (negate (fromInteger i)))
    where
      n = knownNat @n

-- Equivalent to what a derived Show instance would be, except that we
-- intentionally do not print out the (non-exported) _getFin field name.
instance Show (Fin n) where
  showsPrec p i = showParen (p >= 11) $ showString "Fin " . shows (finToNat i)

mkFin :: forall i n. (i + 1 <= n) => NatRepr i -> Fin n
mkFin = Fin
{-# INLINE mkFin #-}

-- | Construct a @'Fin' n@ value from the number @i@, where @i@ is reduced
-- modulo @n@.
mkFinModN :: (1 <= n) => NatRepr n -> NatRepr i -> Fin n
mkFinModN n i = withModLeq i n Fin

newtype Fin' n = Fin' { getFin' :: Fin (n + 1) }

buildFin ::
  forall m.
  NatRepr m ->
  (forall n. (n + 1 <= m) => NatRepr n -> Fin (n + 1) -> Fin (n + 1 + 1)) ->
  Fin (m + 1)
buildFin m f =
  let f' :: forall k. (k + 1 <= m) => NatRepr k -> Fin' k -> Fin' (k + 1)
      f' = (\n (Fin' fin) -> Fin' (f n fin))
  in getFin' (natRecStrictlyBounded m (Fin' minFin) f')

-- | Count all of the numbers up to @m@ that meet some condition.
countFin ::
  NatRepr m ->
  (forall n. (n + 1 <= m) => NatRepr n -> Fin (n + 1) -> Bool) ->
  Fin (m + 1)
countFin m f =
  buildFin m $
    \n count ->
      if f n count
      then incFin count
      else case leqSucc count of
              LeqProof -> embed count

viewFin ::  (forall i. (i + 1 <= n) => NatRepr i -> r) -> Fin n -> r
viewFin f (Fin i) = f i

-- | Construct a @'Fin' n@ value from a 'Natural' input, where the input is
-- reduced modulo @n@.
finFromNatModN :: forall n. (1 <= n) => NatRepr n -> Natural -> Fin n
finFromNatModN n i
  | Some i' <- mkNatRepr i
  = mkFinModN n i'

finToNat :: Fin n -> Natural
finToNat (Fin i) = natValue i
{-# INLINABLE finToNat #-}

embed :: forall n m. (n <= m) => Fin n -> Fin m
embed =
  viewFin
    (\(x :: NatRepr o) ->
      case leqTrans (LeqProof :: LeqProof (o + 1) n) (LeqProof :: LeqProof n m) of
        LeqProof -> Fin x
    )

tryEmbed :: NatRepr n -> NatRepr m -> Fin n -> Maybe (Fin m)
tryEmbed n m i =
  case testLeq n m of
    Just LeqProof -> Just (embed i)
    Nothing -> Nothing

-- | The smallest element of @'Fin' n@
minFin :: (1 <= n) => Fin n
minFin = Fin (knownNat @0)
{-# INLINABLE minFin #-}

incFin :: forall n. Fin n -> Fin (n + 1)
incFin (Fin (i :: NatRepr i)) =
  case leqAdd2 (LeqProof :: LeqProof (i + 1) n) (LeqProof :: LeqProof 1 1) of
    LeqProof -> mkFin (incNat i)

-- | It is not possible to construct an element of @'Fin' 0@.
fin0Absurd :: Fin 0 -> a
fin0Absurd =
  viewFin
    (\(x :: NatRepr o) ->
      case plusComm x (knownNat @1) of
        Refl ->
          case addIsLeqLeft1 @1 @o @0 LeqProof of {})

-- | Add two @'Fin' n@ values and reduce the result modulo @n@.
addFinModN :: (1 <= n) => NatRepr n -> Fin n -> Fin n -> Fin n
addFinModN n (Fin x) (Fin y) = mkFinModN n (addNat x y)

-- | Subtract two @'Fin' n@ values and reduce the result modulo @n@.
subFinModN :: (1 <= n) => NatRepr n -> Fin n -> Fin n -> Fin n
subFinModN n x y = addFinModN n x (negFinModN n y)

-- | Multiply two @'Fin' n@ values and reduce the result modulo @n@.
mulFinModN :: (1 <= n) => NatRepr n -> Fin n -> Fin n -> Fin n
mulFinModN n (Fin x) (Fin y) = mkFinModN n (natMultiply x y)

-- | Given a value @i :: 'Fin' n@ value, negate it. That is, if @i@ is zero,
-- then return @i@ unchanged, and if @i@ is non-zero, then compute @n - i@.
-- This is a negation in the sense that it is an additive inverse: adding @i@
-- to its negation will yield 'minFin'.
negFinModN :: forall n. (1 <= n) => NatRepr n -> Fin n -> Fin n
negFinModN n (Fin (i :: NatRepr i))
  | LeqProof <- addIsLeqLeft1 @i @1 @n LeqProof
  = mkFinModN n (subNat n i)

-- | Given a value @i :: 'Fin' n@, compute the reciprocal (i.e., the modular
-- inverse) if one exists. That is, attempt to compute @i^-1@ such that
-- @i * i^-1@ equals @1@ modulo @n@. Note that a reciprocal will only exist if
-- @i@ and @n@ are relatively prime, i.e., if @gcd i n == 1@. If they are not
-- relatively prime, then this function will return 'Nothing'.
--
-- Note that in the degenerate case where @n == 1@, this function will always
-- return @Just 0@. The value @0@ is the only element of @'Fin' 1@, and @0@ is
-- its own reciprocal.
recipFinModN :: forall n. (1 <= n) => NatRepr n -> Fin n -> Maybe (Fin n)
recipFinModN n (Fin i) = withRecipModNat i n Fin
