{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Parameterized.DataKind
  ( PairRepr(..), Fst, Snd, fst, snd
  ) where

import           Data.Parameterized.Classes
import qualified Data.Parameterized.TH.GADT as TH

import           Data.Kind
import           Prelude hiding ( fst, snd )

data PairRepr (f :: k1 -> Type) (g :: k2 -> Type) (p :: (k1, k2)) where
  PairRepr :: f a -> g b -> PairRepr f g '(a, b)

type family Fst (pair :: (k1, k2)) where
  Fst '(a, _) = a
type family Snd (pair :: (k1, k2)) where
  Snd '(_, b) = b

fst :: PairRepr f g p -> f (Fst p)
fst (PairRepr a _) = a

snd :: PairRepr f g p -> g (Snd p)
snd (PairRepr _ b) = b

$(return [])

instance ( ShowF f, ShowF g ) => Show (PairRepr f g p) where
  show (PairRepr a b) = showChar '(' . showsF a . showChar ',' . showsF b $ ")"
instance ( ShowF f, ShowF g ) => ShowF (PairRepr f g)

deriving instance ( Eq (f a), Eq (g b) ) => Eq (PairRepr f g '(a, b))
instance ( EqF f, EqF g ) => EqF (PairRepr f g) where
  eqF (PairRepr a1 b1) (PairRepr a2 b2) =
    eqF a1 a2 && eqF b1 b2
instance ( TestEquality f, TestEquality g ) => TestEquality (PairRepr f g) where
  testEquality =
    $(TH.structuralTypeEquality [t|PairRepr|]
      [
        ( TH.DataArg 0 `TH.TypeApp` TH.AnyType, [|testEquality|] )
      , ( TH.DataArg 1 `TH.TypeApp` TH.AnyType, [|testEquality|] )
      ])

deriving instance ( Ord (f a), Ord (g b) ) => Ord (PairRepr f g '(a, b))
instance ( OrdF f, OrdF g ) => OrdF (PairRepr f g) where
  compareF =
    $(TH.structuralTypeOrd [t|PairRepr|]
      [ ( TH.DataArg 0 `TH.TypeApp` TH.AnyType, [|compareF|] )
      , ( TH.DataArg 1 `TH.TypeApp` TH.AnyType, [|compareF|] )
      ])
