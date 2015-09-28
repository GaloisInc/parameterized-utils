------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.SymbolRepr
-- Description      : Data-type for representing a type-level Symbol.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This defines a type family @SymbolRepr@ for representing a type-level
-- string (AKA symbol) at runtime.
-- This can be used to branch on a type-level value.  For
-- each @nm@, @SymbolRepr nm@ contains a single value containing the string
-- value of @nm@.  This can be used to help use type-level variables on code
-- with data dependendent types.
--
-- The @TestEquality@ and @OrdF@ instances for @SymbolRepr@ are implemented using
-- @unsafeCoerce@.  This should be typesafe because we maintain the invariant
-- that the string value contained in a SymolRepr value matches its static type.
--
-- At the type level, symbols have basically no operations, so SymbolRepr
-- correspondingly has very few functions that manipulate them.
------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE PatternGuards #-}
module Data.Parameterized.SymbolRepr
  ( type GHC.Symbol
  , GHC.KnownSymbol
  , SymbolRepr
  , symbolRepr
  , knownSymbol
  ) where

import GHC.TypeLits as GHC
import Unsafe.Coerce (unsafeCoerce)

import Data.Hashable
import Data.Proxy

import Data.Parameterized.Classes

-- INVARIANT: The contained runtime string matches the value
-- of the type level symbol.  The SymbolRepr constructor
-- is not exported so we can maintain this invariant in this
-- module.
newtype SymbolRepr (nm::GHC.Symbol)
  = SymbolRepr { symbolRepr :: String }

-- | Generate a value representative for the type level
--   symbol.  This is the only way to generate values
--   of `SymbolRepr`.
knownSymbol :: GHC.KnownSymbol s => SymbolRepr s
knownSymbol = go Proxy
  where go :: GHC.KnownSymbol s => Proxy s -> SymbolRepr s
        go p = SymbolRepr (GHC.symbolVal p)

instance TestEquality SymbolRepr where
   testEquality (SymbolRepr x :: SymbolRepr x) (SymbolRepr y)
      | x == y    = Just (unsafeCoerce (Refl :: x :~: x))
      | otherwise = Nothing
instance OrdF SymbolRepr where
   compareF (SymbolRepr x :: SymbolRepr x) (SymbolRepr y)
      | x <  y    = LTF
      | x == y    = unsafeCoerce (EQF :: OrderingF x x)
      | otherwise = GTF

-- These instances are trivial by the invariant
-- that the contained string matches the type-level
-- symbol
instance Eq (SymbolRepr x) where
   _ == _ = True
instance Ord (SymbolRepr x) where
   compare _ _ = EQ

instance HashableF SymbolRepr where
  hashWithSaltF = hashWithSalt
instance Hashable (SymbolRepr nm) where
  hashWithSalt s (SymbolRepr nm) = hashWithSalt s nm

instance ShowF SymbolRepr where
  showF = show
instance Show (SymbolRepr nm) where
  show (SymbolRepr nm) = nm
