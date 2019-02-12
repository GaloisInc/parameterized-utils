{-|

This defines a type 'Peano' and 'PeanoRepr' for representing a
type-level natural at runtime. These type-level numbers are defined
inductively instead of using GHC.TypeLits.

As a result, type-level computation defined recursively over these
numbers works more smoothly. (For example, see the type-level
function Repeatn below.)

Note: as in NatRepr, the runtime representation of these type-level
natural numbers is an Int.

-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

#if MIN_VERSION_base(4,9,0)
{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}
#endif
#if __GLASGOW_HASKELL__ >= 805
{-# LANGUAGE NoStarIsType #-}
#endif
module Data.Parameterized.Peano
   ( Peano
     , Z , S
     , Plus, Minus, Mul, Le, Lt, Gt, Ge, Max, Min, Repeat
     , plusP, minusP, mulP, maxP, minP, repeatP
     , zeroP, succP, predP

     , KnownPeano
     , withKnownPeano

     , PeanoRepr, peanoValue
     , PeanoView(..), peanoView
     , viewRepr

     , somePeano
     , mkPeanoRepr
     , maxPeano
     , minPeano

     -- * Re-exports
     , TestEquality(..)
     , (:~:)(..)
     , Data.Parameterized.Some.Some

     ) where

import           Data.Parameterized.Classes
import           Data.Parameterized.DecidableEq
import           Data.Parameterized.Some

import           Data.Hashable
import           Data.Constraint
import           Data.Word

import           Unsafe.Coerce(unsafeCoerce)

------------------------------------------------------------------------
-- ** Peano - a unary representation of natural numbers

data Peano = Z | S Peano
-- | Peano zero
type Z = 'Z
-- | Peano successor
type S = 'S

-- Peano numbers are more about *counting* than arithmetic.
-- They are most useful as iteration arguments and list indices
-- However, for completeness, we define a few standard
-- operations.

type family Plus (a :: Peano) (b :: Peano) :: Peano where
  Plus Z     b = b
  Plus (S a) b = S (Plus a b)

type family Minus (a :: Peano) (b :: Peano) :: Peano where
  Minus Z     b     = Z
  Minus (S a) (S b) = Minus a b
  Minus a    Z      = a

type family Mul (a :: Peano) (b :: Peano) :: Peano where
  Mul Z     b = Z
  Mul (S a) b = Plus a (Mul a b)

type family Le  (a :: Peano) (b :: Peano) :: Bool where
  Le  a  a        = 'True
  Le  Z  b        = 'True
  Le  a  Z        = 'False
  Le  (S a) (S b) = Le a b

type family Lt  (a :: Peano) (b :: Peano) :: Bool where
  Lt a b = Le (S a) b

type family Gt  (a :: Peano) (b :: Peano) :: Bool where
  Gt a b = Lt b a

type family Ge  (a :: Peano) (b :: Peano) :: Bool where
  Ge a b = Le b a

type family Max (a :: Peano) (b :: Peano) :: Peano where
  Max Z b = b
  Max a Z = a
  Max (S a) (S b) = S (Max a b)

type family Min (a :: Peano) (b :: Peano) :: Peano where
  Min Z b = Z
  Min a Z = Z
  Min (S a) (S b) = S (Min a b)

-- Apply a constructor 'f' n-times to an argument 's'
type family Repeat (m :: Peano) (f :: k -> k) (s :: k) :: k where
  Repeat Z f s     = s
  Repeat (S m) f s = f (Repeat m f s)


------------------------------------------------------------------------
-- ** Run time representation of Peano numbers

-- | The run time value, stored as an Word64
-- As these are unary numbers, we don't worry about overflow.
newtype PeanoRepr (n :: Peano) =
  PeanoRepr { peanoValue :: Word64 }

-- n is Phantom in the definition, but we don't want to allow coerce
type role PeanoRepr nominal

----------------------------------------------------------

-- | Because we have optimized the runtime representation,
-- we need to have a "view" that decomposes the representation
-- into the standard form.
data PeanoView (n :: Peano) where
  ZRepr :: PeanoView Z
  SRepr :: PeanoRepr n -> PeanoView (S n)

-- | Test whether a number is Zero or Successor
peanoView :: PeanoRepr n -> PeanoView n
peanoView (PeanoRepr i) =
  if i == 0 then unsafeCoerce ZRepr else unsafeCoerce (SRepr (PeanoRepr (i-1)))

-- | convert the view back to the runtime representation
viewRepr :: PeanoView n -> PeanoRepr n
viewRepr ZRepr     = PeanoRepr 0
viewRepr (SRepr n) = PeanoRepr (peanoValue n + 1)

----------------------------------------------------------

instance Hashable (PeanoRepr n) where
  hashWithSalt i (PeanoRepr x) = hashWithSalt i x

instance Eq (PeanoRepr m) where
  _ == _ = True

instance TestEquality PeanoRepr where
  testEquality (PeanoRepr m) (PeanoRepr n)
    | m == n = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance DecidableEq PeanoRepr where
  decEq (PeanoRepr m) (PeanoRepr n)
    | m == n    = Left $ unsafeCoerce Refl
    | otherwise = Right $
        \x -> seq x $ error "Impossible [DecidableEq on PeanoRepr]"

instance OrdF PeanoRepr where
  compareF (PeanoRepr m) (PeanoRepr n)
    | m < n     = unsafeCoerce LTF
    | m == n    = unsafeCoerce EQF
    | otherwise = unsafeCoerce GTF

instance PolyEq (PeanoRepr m) (PeanoRepr n) where
  polyEqF x y = (\Refl -> Refl) <$> testEquality x y

-- Display as digits, not in unary
instance Show (PeanoRepr p) where
  show p = show (peanoValue p)

instance ShowF PeanoRepr

instance HashableF PeanoRepr where
  hashWithSaltF = hashWithSalt

----------------------------------------------------------
-- * Implicit runtime Peano numbers

type KnownPeano = KnownRepr PeanoRepr

instance KnownRepr PeanoRepr Z where
  knownRepr = viewRepr ZRepr
instance (KnownRepr PeanoRepr n) => KnownRepr PeanoRepr (S n) where
  knownRepr = viewRepr (SRepr knownRepr)

newtype DI a = Don'tInstantiate (KnownPeano a => Dict (KnownPeano a))

peanoInstance :: forall a . PeanoRepr a -> Dict (KnownPeano a)
peanoInstance s = with_sing_i Dict
  where
    with_sing_i :: (KnownPeano a => Dict (KnownPeano a)) -> Dict (KnownPeano a)
    with_sing_i si = unsafeCoerce (Don'tInstantiate si) s

-- | convert an explicit number to an implicit number
withKnownPeano :: forall n r. PeanoRepr n -> (KnownPeano n => r) -> r
withKnownPeano si r = case peanoInstance si of
                        Dict -> r

----------------------------------------------------------
-- * Operations on runtime numbers

-- | zero
zeroP :: PeanoRepr Z
zeroP = PeanoRepr 0

-- | Successor, Increment
succP :: PeanoRepr n -> PeanoRepr (S n)
succP (PeanoRepr i) = PeanoRepr (i+1)

-- | Get the predecessor (decrement)
predP :: PeanoRepr (S n) -> PeanoRepr n
predP (PeanoRepr i) = PeanoRepr (i-1)


plusP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Plus a b)
plusP (PeanoRepr a) (PeanoRepr b) = PeanoRepr (a + b)

minusP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Minus a b)
minusP (PeanoRepr a) (PeanoRepr b) = PeanoRepr (a - b)

mulP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Mul a b)
mulP (PeanoRepr a) (PeanoRepr b) = PeanoRepr (a * b)

maxP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Max a b)
maxP (PeanoRepr a) (PeanoRepr b) = PeanoRepr (max a b)

minP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Min a b)
minP (PeanoRepr a) (PeanoRepr b) = PeanoRepr (min a b)

repeatP :: PeanoRepr m -> (forall a. repr a -> repr (f a)) -> repr s -> repr (Repeat m f s)
repeatP n f s = case peanoView n of
  ZRepr   -> s
  SRepr m -> f (repeatP m f s)

------------------------------------------------------------------------
-- * Some PeanoRepr

-- | Convert a Word64 to a PeanoRepr
mkPeanoRepr :: Word64 -> Some PeanoRepr
mkPeanoRepr n = Some (PeanoRepr n)

-- | Turn an @Integral@ value into a @PeanoRepr@.  Returns @Nothing@
--   if the given value is negative.
somePeano :: Integral a => a -> Maybe (Some PeanoRepr)
somePeano x | x >= 0 = Just . Some . PeanoRepr $! fromIntegral x
somePeano _ = Nothing

-- | Return the maximum of two representations.
maxPeano :: PeanoRepr m -> PeanoRepr n -> Some PeanoRepr
maxPeano x y
  | peanoValue x >= peanoValue y = Some x
  | otherwise = Some y

-- | Return the minimum of two representations.
minPeano :: PeanoRepr m -> PeanoRepr n -> Some PeanoRepr
minPeano x y
  | peanoValue y >= peanoValue x = Some x
  | otherwise = Some y

------------------------------------------------------------------------
--  LocalWords:  PeanoRepr withKnownPeano runtime Peano unary
