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

module Data.Parameterized.BoolRepr
  ( module Data.Type.Bool
  , BoolRepr(..)
  , ifRepr, notRepr, (%&&), (%||)
  , KnownBool

  , someBool

  -- * Re-exports
  , TestEquality(..)
  , (:~:)(..)
  , Data.Parameterized.Some.Some
  )
where

import           Data.Parameterized.Classes
import           Data.Parameterized.DecidableEq
import           Data.Parameterized.Some

import           Data.Type.Bool

-- | A Boolean flag
data BoolRepr (b :: Bool) where
  FalseRepr :: BoolRepr 'False
  TrueRepr  :: BoolRepr 'True

-- | conditional
ifRepr :: BoolRepr a -> BoolRepr b -> BoolRepr c -> BoolRepr (If a b c)
ifRepr TrueRepr b _ = b
ifRepr FalseRepr _ c = c

-- | negation
notRepr :: BoolRepr b -> BoolRepr (Not b)
notRepr TrueRepr = FalseRepr
notRepr FalseRepr = TrueRepr

-- | Conjunction
(%&&) :: BoolRepr a -> BoolRepr b -> BoolRepr (a && b)
FalseRepr %&& _ = FalseRepr
TrueRepr  %&& a = a
infixr 3 %&&

-- | Disjunction
(%||) :: BoolRepr a -> BoolRepr b -> BoolRepr (a || b)
FalseRepr %|| a = a
TrueRepr  %|| _ = TrueRepr
infixr 2 %||

instance Hashable (BoolRepr n) where
  hashWithSalt i TrueRepr  = hashWithSalt i True
  hashWithSalt i FalseRepr = hashWithSalt i False


instance Eq (BoolRepr m) where
  _ == _ = True

instance EqF BoolRepr where
  eqF _ _ = True

instance TestEquality BoolRepr where
  testEquality TrueRepr TrueRepr   = Just Refl
  testEquality FalseRepr FalseRepr = Just Refl
  testEquality _ _ = Nothing

instance DecidableEq BoolRepr where
  decEq TrueRepr  TrueRepr  = Left Refl
  decEq FalseRepr FalseRepr = Left Refl
  decEq TrueRepr  FalseRepr = Right $ \case {}
  decEq FalseRepr TrueRepr  = Right $ \case {}

instance OrdF BoolRepr where
  compareF TrueRepr  TrueRepr  = EQF
  compareF FalseRepr FalseRepr = EQF
  compareF TrueRepr  FalseRepr = GTF
  compareF FalseRepr TrueRepr  = LTF

instance PolyEq (BoolRepr m) (BoolRepr n) where
  polyEqF x y = (\Refl -> Refl) <$> testEquality x y

instance Show (BoolRepr m) where
  show FalseRepr = "FalseRepr"
  show TrueRepr  = "TrueRepr"

instance ShowF BoolRepr

instance HashableF BoolRepr where
  hashWithSaltF = hashWithSalt

----------------------------------------------------------
-- * Implicit runtime booleans

type KnownBool = KnownRepr BoolRepr

instance KnownRepr BoolRepr 'True where
  knownRepr = TrueRepr
instance KnownRepr BoolRepr 'False where
  knownRepr = FalseRepr

someBool :: Bool -> Some BoolRepr
someBool True  = Some TrueRepr
someBool False = Some FalseRepr
