------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.FreeParamF
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- A wrapper for converting an unparameterized type to a parameterized type.
--
-- This is essentially the opposite of @Data.Parameterized.Some@.
------------------------------------------------------------------------
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Safe #-}
module Data.Parameterized.FreeParamF
  ( FreeParamF(..)
  ) where

newtype FreeParamF (a :: *) (b :: k) =
  FreeParamF { unFreeParamF :: a }
