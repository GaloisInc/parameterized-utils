------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.All
-- Copyright        : (c) Galois, Inc 2019
-- Maintainer       : Langston Barrett <langston@galois.com>
-- Description      : Universal quantification, in a datatype
--
-- This module provides 'All', a GADT that encodes universal
-- quantification/parametricity over a type variable.
--
-- The following is an example of a situation in which it might be necessary
-- to use 'All' (though it is a bit contrived):
--
-- @
--   {-# LANGUAGE FlexibleInstances #-}
--   {-# LANGUAGE GADTs #-}
--
--   data F (x :: Bool) where
--     FTrue :: F 'True
--     FFalse :: F 'False
--     FIndeterminate :: F b
--
--   data Value =
--     VAllF (All F)
--
--   class Valuable a where
--     valuation :: a -> Value
--
--   instance Valuable (All F) where
--     valuation = VAllF
--
--   val1 :: Value
--   val1 = valuation (All FIndeterminate)
-- @
--
-- For a less contrived but more complex example, see this blog
-- post: http://comonad.com/reader/2008/rotten-bananas/
------------------------------------------------------------------------

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Data.Parameterized.All
  ( All(..)
  , allConst
  ) where

import Data.Functor.Const (Const(..))
import Data.Kind

import Data.Parameterized.Classes
import Data.Parameterized.TraversableF

newtype All (f :: k -> Type) = All { getAll :: forall x. f x }

instance FunctorF All where
  fmapF f (All a) = All (f a)

instance FoldableF All where
  foldMapF toMonoid (All x) = toMonoid x

instance ShowF f => Show (All f) where
  show (All fa) = showF fa

instance EqF f => Eq (All f) where
  (All x) == (All y) = eqF x y

allConst :: a -> All (Const a)
allConst a = All (Const a)
