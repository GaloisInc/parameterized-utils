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
  , buildFin
  , countFin
  , viewFin
  , finToNat
  , embed
  , tryEmbed
  , minFin
  , incFin
  , fin0Void
  , fin1Unit
  , fin2Bool
  ) where

import Data.Void (Void, absurd)
import GHC.TypeNats (KnownNat)
import Lens.Micro.Pro (Iso', iso)
import Numeric.Natural (Natural)

import Data.Parameterized.NatRepr

-- | The type @'Fin' n@ has exactly @n@ inhabitants.
data Fin n =
  -- GHC 8.6 and 8.4 require parentheses around 'i + 1 <= n'
  forall i. (i + 1 <= n) => Fin { _getFin :: NatRepr i }

instance Eq (Fin n) where
  i == j = finToNat i == finToNat j

instance Ord (Fin n) where
  compare i j = compare (finToNat i) (finToNat j)

instance (1 <= n, KnownNat n) => Bounded (Fin n) where
  minBound = Fin (knownNat @0)
  maxBound =
    case minusPlusCancel (knownNat @n) (knownNat @1) of
      Refl -> Fin (decNat (knownNat @n))

-- | Non-lawful instance, intended only for testing.
instance Show (Fin n) where
  show i = "Fin " ++ show (finToNat i)

mkFin :: forall i n. (i + 1 <= n) => NatRepr i -> Fin n
mkFin = Fin
{-# INLINE mkFin #-}

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

fin0Void :: Iso' (Fin 0) Void
fin0Void =
  iso
    (viewFin
      (\(x :: NatRepr o) ->
        case plusComm x (knownNat @1) of
          Refl ->
            case addIsLeqLeft1 @1 @o @0 LeqProof of {}))
    absurd

fin1Unit :: Iso' (Fin 1) ()
fin1Unit = iso (const ()) (const minFin)

fin2Bool :: Iso' (Fin 2) Bool
fin2Bool =
  iso
    (viewFin
      (\n ->
         case isZeroNat n of
           ZeroNat -> False
           NonZeroNat -> True))
    (\b -> if b then maxBound else minBound)

{-# DEPRECATED
  fin0Void, fin1Unit, fin2Bool
  "These will be removed in the next release of parameterized-utils, see #208."
#-}
