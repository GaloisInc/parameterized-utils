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
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
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
     , Plus, Minus, Mul,  Max, Min
     , plusP, minusP, mulP, maxP, minP
     , zeroP, succP, predP
     , Repeat, CtxSizeP
     , repeatP, ctxSizeP

     , Le, Lt, Gt, Ge
     , leP, ltP, gtP, geP
     
     , KnownPeano

     , PeanoRepr, peanoValue
     , PeanoView(..), peanoView
     , viewRepr

     , somePeano
     , peanoLength
     
     , mkPeanoRepr
     , maxPeano
     , minPeano

     , plusCtxSizeAxiom
     , minusPlusAxiom
     , ltMinusPlusAxiom

     -- * Re-exports
     , TestEquality(..)
     , (:~:)(..)
     , Data.Parameterized.Some.Some

     ) where

import           Data.Parameterized.BoolRepr
import           Data.Parameterized.Classes
import           Data.Parameterized.DecidableEq
import           Data.Parameterized.Some
import           Data.Parameterized.Context

import           Data.Hashable
import           Data.Word

#ifdef UNSAFE_OPS
import           Unsafe.Coerce(unsafeCoerce)
#endif

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
  Le  Z  b        = 'True
  Le  a  Z        = 'False
  Le  (S a) (S b) = Le a b

type family Lt  (a :: Peano) (b :: Peano) :: Bool where
  Lt a b = Le (S a) b

type family Gt  (a :: Peano) (b :: Peano) :: Bool where
  Gt a b = Le b a

type family Ge  (a :: Peano) (b :: Peano) :: Bool where
  Ge a b = Lt b a

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

-- Calculate the size of a context
type family CtxSizeP (ctx :: Ctx k) :: Peano where
  CtxSizeP 'EmptyCtx   = Z
  CtxSizeP (xs '::> x) = S (CtxSizeP xs)

------------------------------------------------------------------------
-- ** Run time representation of Peano numbers

-- | The run time value, stored as an Word64
-- As these are unary numbers, we don't worry about overflow.
#ifdef UNSAFE_OPS
newtype PeanoRepr (n :: Peano) =
  PeanoRepr { peanoValue :: Word64 }
-- n is Phantom in the definition, but we don't want to allow coerce
type role PeanoRepr nominal
#else
type PeanoRepr = PeanoView
peanoValue :: PeanoRepr n -> Word64
peanoValue ZRepr     = 0
peanoValue (SRepr m) = 1 + peanoValue m
#endif
                                    

----------------------------------------------------------

-- | Because we have optimized the runtime representation,
-- we need to have a "view" that decomposes the representation
-- into the standard form.
data PeanoView (n :: Peano) where
  ZRepr :: PeanoView Z
  SRepr :: PeanoRepr n -> PeanoView (S n)

-- | Test whether a number is Zero or Successor
peanoView :: PeanoRepr n -> PeanoView n
#ifdef UNSAFE_OPS
peanoView (PeanoRepr i) =
  if i == 0
  then unsafeCoerce ZRepr
  else unsafeCoerce (SRepr (PeanoRepr (i-1)))
#else
peanoView = id
#endif

-- | convert the view back to the runtime representation
viewRepr :: PeanoView n -> PeanoRepr n
#ifdef UNSAFE_OPS
viewRepr ZRepr     = PeanoRepr 0
viewRepr (SRepr n) = PeanoRepr (peanoValue n + 1)
#else
viewRepr = id
#endif

----------------------------------------------------------

instance Hashable (PeanoRepr n) where
  hashWithSalt i x = hashWithSalt i (peanoValue x)

instance Eq (PeanoRepr m) where
  _ == _ = True

instance TestEquality PeanoRepr where
#ifdef UNSAFE_OPS
  testEquality (PeanoRepr m) (PeanoRepr n)
    | m == n = Just (unsafeCoerce Refl)
    | otherwise = Nothing
#else 
  testEquality ZRepr ZRepr = Just Refl
  testEquality (SRepr m1) (SRepr m2)
    | Just Refl <- testEquality m1 m2
    = Just Refl
  testEquality _ _ = Nothing
  
#endif

instance DecidableEq PeanoRepr where
#ifdef UNSAFE_OPS
  decEq (PeanoRepr m) (PeanoRepr n)
    | m == n    = Left $ unsafeCoerce Refl
    | otherwise = Right $
        \x -> seq x $ error "Impossible [DecidableEq on PeanoRepr]"
#else
  decEq ZRepr ZRepr = Left Refl
  decEq (SRepr m1) (SRepr m2) =
    case decEq m1 m2 of
      Left Refl -> Left Refl
      Right f   -> Right $ \case Refl -> f Refl
  decEq ZRepr (SRepr _) =
      Right $ \case {}
  decEq (SRepr _) ZRepr =
      Right $ \case {}
#endif

instance OrdF PeanoRepr where
#ifdef UNSAFE_OPS
  compareF (PeanoRepr m) (PeanoRepr n)
    | m < n     = unsafeCoerce LTF
    | m == n    = unsafeCoerce EQF
    | otherwise = unsafeCoerce GTF
#else
  compareF ZRepr      ZRepr      = EQF
  compareF ZRepr      (SRepr _)  = LTF
  compareF (SRepr _)  ZRepr      = GTF
  compareF (SRepr m1) (SRepr m2) =
    case compareF m1 m2 of
       EQF -> EQF
       LTF -> LTF
       GTF -> GTF
#endif

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

----------------------------------------------------------
-- * Operations on runtime numbers

#ifdef UNSAFE_OPS
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


leP :: PeanoRepr a -> PeanoRepr b -> BoolRepr (Le a b)
leP  (PeanoRepr a) (PeanoRepr b) =
  if a <= b then unsafeCoerce (TrueRepr)
            else unsafeCoerce(FalseRepr)


#else
zeroP :: PeanoRepr Z
zeroP = ZRepr

-- | Successor, Increment
succP :: PeanoRepr n -> PeanoRepr (S n)
succP = SRepr

-- | Get the predecessor (decrement)
predP :: PeanoRepr (S n) -> PeanoRepr n
predP (SRepr i) = i


plusP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Plus a b)
plusP ZRepr     b = b
plusP (SRepr a) b = SRepr (plusP a b)

minusP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Minus a b)
minusP ZRepr     _b        = ZRepr
minusP (SRepr a) (SRepr b) = minusP a b
minusP a ZRepr             = a

mulP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Mul a b)
mulP ZRepr     _b = ZRepr
mulP (SRepr a) b  = plusP a (mulP a b)

maxP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Max a b)
maxP ZRepr     b         = b
maxP a         ZRepr     = a
maxP (SRepr a) (SRepr b) = SRepr (maxP a b)

minP :: PeanoRepr a -> PeanoRepr b -> PeanoRepr (Min a b)
minP ZRepr     _b        = ZRepr
minP _a        ZRepr     = ZRepr
minP (SRepr a) (SRepr b) = SRepr (minP a b)

leP :: PeanoRepr a -> PeanoRepr b -> BoolRepr (Le a b)
leP ZRepr      ZRepr    = TrueRepr
leP ZRepr     (SRepr _) = TrueRepr
leP (SRepr _) ZRepr     = FalseRepr
leP (SRepr a) (SRepr b) = leP a b

#endif


ltP :: PeanoRepr a -> PeanoRepr b -> BoolRepr (Lt a b)
ltP a b = leP (succP a) b

geP :: PeanoRepr a -> PeanoRepr b -> BoolRepr (Ge a b)
geP a b = ltP b a

gtP :: PeanoRepr a -> PeanoRepr b -> BoolRepr (Gt a b)
gtP a b = leP b a



repeatP :: PeanoRepr m -> (forall a. repr a -> repr (f a)) -> repr s -> repr (Repeat m f s)
repeatP n f s = case peanoView n of
  ZRepr   -> s
  SRepr m -> f (repeatP m f s)

ctxSizeP :: Assignment f ctx -> PeanoRepr (CtxSizeP ctx)
ctxSizeP r = case viewAssign r of
  AssignEmpty -> zeroP
  AssignExtend a _ -> succP (ctxSizeP a)

------------------------------------------------------------------------
-- * Some PeanoRepr

-- | Convert a Word64 to a PeanoRepr
mkPeanoRepr :: Word64 -> Some PeanoRepr
#ifdef UNSAFE_OPS
mkPeanoRepr n = Some (PeanoRepr n)
#else
mkPeanoRepr 0 = Some ZRepr
mkPeanoRepr n = case mkPeanoRepr (n - 1) of
                 Some mr -> Some (SRepr mr)
#endif                 

-- | Turn an @Integral@ value into a @PeanoRepr@.  Returns @Nothing@
--   if the given value is negative.
somePeano :: Integral a => a -> Maybe (Some PeanoRepr)
somePeano x | x >= 0 = Just . mkPeanoRepr $! fromIntegral x
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

-- | List length as a Peano number
peanoLength :: [a] -> Some PeanoRepr
peanoLength [] = Some zeroP
peanoLength (_:xs) = case peanoLength xs of
  Some n -> Some (succP n)


------------------------------------------------------------------------
-- Some properties about Peano numbers

plusCtxSizeAxiom :: forall t1 t2 f.
  Assignment f t1 -> Assignment f t2 ->
  CtxSizeP (t1 <+> t2) :~: Plus (CtxSizeP t2) (CtxSizeP t1)
#ifdef UNSAFE_OPS
plusCtxSizeAxiom _t1 _t2 = unsafeCoerce Refl
#else
plusCtxSizeAxiom t1 t2 =
  case viewAssign t2 of
    AssignEmpty -> Refl
    AssignExtend t2' _
      | Refl <- plusCtxSizeAxiom t1 t2' -> Refl
#endif


minusPlusAxiom :: forall n t t'.
  PeanoRepr n -> PeanoRepr t -> PeanoRepr t' ->    
  Minus n (Plus t' t) :~: Minus (Minus n t') t
#ifdef UNSAFE_OPS
minusPlusAxiom _n _t _t' = unsafeCoerce Refl
#else
minusPlusAxiom n t t' = case peanoView t' of
  ZRepr -> Refl
  SRepr t1' -> case peanoView n of
      ZRepr -> Refl
      SRepr n1 -> case minusPlusAxiom n1 t t1' of
        Refl -> Refl
#endif

ltMinusPlusAxiom :: forall n t t'.
  (Lt t (Minus n t') ~ 'True) =>
  PeanoRepr n -> PeanoRepr t -> PeanoRepr t' ->
  Lt (Plus t' t) n :~: 'True
#ifdef UNSAFE_OPS
ltMinusPlusAxiom _n _t _t' = unsafeCoerce Refl
#else
ltMinusPlusAxiom n t t' = case peanoView n of
  SRepr m -> case peanoView t' of
     ZRepr -> Refl
     SRepr t1' -> case ltMinusPlusAxiom m t t1' of
        Refl -> Refl
#endif

------------------------------------------------------------------------
--  LocalWords:  PeanoRepr withKnownPeano runtime Peano unary
