------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Ctx
-- Copyright        : (c) Galois, Inc 2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- This module defines type-level lists used for representing the type of
-- variables in a context.
--------------------------------------------------------------------------
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.Ctx
  ( type Ctx(..)
  , EmptyCtx
  , (::>)
  ) where

------------------------------------------------------------------------
-- Ctx

type EmptyCtx = 'EmptyCtx
type (c ::Ctx k) ::> (a::k)  = c '::> a

-- | A kind representing a hetergenous list of values in some key.
-- The parameter a, may be any kind.
data Ctx a
  = EmptyCtx
  | Ctx a ::> a

type family (<+>) (x :: Ctx k) (y :: Ctx k) :: Ctx k where
  x <+> EmptyCtx = x
  x <+> (y ::> e) = (x <+> y) ::> e
