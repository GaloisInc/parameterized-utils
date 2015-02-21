------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Ctx
-- Description      : Finite dependent products
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines type contexts as a data-kind that consists of
-- a list of types.  It is used to implement SafeContext and UnsafeContext.
--------------------------------------------------------------------------
module Data.Parameterized.Ctx
  ( Ctx(..)
  ) where

------------------------------------------------------------------------
-- Ctx

-- | A kind representing a hetergenous list of values in some key.
-- The parameter a, may be any kind.
data Ctx a
  = EmptyCtx
  | Ctx a ::> a
