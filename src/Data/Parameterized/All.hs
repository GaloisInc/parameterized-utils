------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.All
-- Copyright        : (c) Galois, Inc 2014-2019
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Description      : Universal quantification, in a datatype
--
-- This module provides 'All', a GADT that encodes universal
-- quantification/parametricity over a type variable
------------------------------------------------------------------------

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Data.Parameterized.All
  ( All(..)
  , allConst
  ) where

import Data.Functor.Const (Const(..))

import Data.Parameterized.Classes
import Data.Parameterized.TraversableF

newtype All (f :: k -> *) = All { getAll :: forall x. f x }

instance FunctorF All where
  fmapF nat (All a) = All (nat a)

instance FoldableF All where
  foldMapF toMonoid (All x) = toMonoid x

instance ShowF f => Show (All f) where
  show (All fa) = showF fa

instance EqF f => Eq (All f) where
  (All x) == (All y) = eqF x y

allConst :: a -> All (Const a)
allConst a = All (Const a)
