{-|
Copyright        : (c) Galois, Inc 2014-2018
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This internal module exports the 'NatRepr' type and its constructor. It is intended
for use only within parameterized-utils, and is excluded from the module export list.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Parameterized.NatRepr.Internal where

import Data.Data
import Data.Hashable
import GHC.TypeNats
import qualified Numeric.Natural as Natural
import Unsafe.Coerce

import Data.Parameterized.Axiom
import Data.Parameterized.Classes
import Data.Parameterized.DecidableEq

------------------------------------------------------------------------
-- Nat

-- | A runtime presentation of a type-level 'Nat'.
--
-- This can be used for performing dynamic checks on a type-level natural
-- numbers.
newtype NatRepr (n::Nat) = NatRepr { natValue :: Natural.Natural
                                     -- ^ The underlying natural value of the number.
                                   }
  deriving (Hashable, Data)

type role NatRepr nominal

instance Eq (NatRepr m) where
  _ == _ = True

instance EqF NatRepr where
  eqF _ _ = True

instance TestEquality NatRepr where
  testEquality (NatRepr m) (NatRepr n)
    | m == n = Just unsafeAxiom
    | otherwise = Nothing

instance DecidableEq NatRepr where
  decEq (NatRepr m) (NatRepr n)
    | m == n    = Left unsafeAxiom
    | otherwise = Right $
        \x -> seq x $ error "Impossible [DecidableEq on NatRepr]"

compareNat :: NatRepr m -> NatRepr n -> NatComparison m n
compareNat m n =
  case compare (natValue m) (natValue n) of
    LT -> unsafeCoerce (NatLT @0 @0) (NatRepr (natValue n - natValue m - 1))
    EQ -> unsafeCoerce  NatEQ
    GT -> unsafeCoerce (NatGT @0 @0) (NatRepr (natValue m - natValue n - 1))

-- | Result of comparing two numbers.
data NatComparison m n where
  -- First number is less than second.
  NatLT :: x+1 <= x+(y+1) => !(NatRepr y) -> NatComparison x (x+(y+1))
  NatEQ :: NatComparison x x
  -- First number is greater than second.
  NatGT :: x+1 <= x+(y+1) => !(NatRepr y) -> NatComparison (x+(y+1)) x

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
