{-|
Description      : Type-level lists.
Copyright        : (c) Galois, Inc 2015
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module defines type-level lists used for representing the type of
variables in a context.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.Ctx
  ( type Ctx(..)
  , EmptyCtx
  , SingleCtx
  , (::>)
  , type (<+>)
  ) where

------------------------------------------------------------------------
-- Ctx

type EmptyCtx = 'EmptyCtx
type (c :: Ctx k) ::> (a::k) = c '::> a

type SingleCtx x = EmptyCtx ::> x

-- | Kind @'Ctx' k@ comprises lists of types of kind @k@.
data Ctx k
  = EmptyCtx
  | Ctx k ::> k

-- | Append two type-level contexts.
type family (<+>) (x :: Ctx k) (y :: Ctx k) :: Ctx k where
  x <+> EmptyCtx = x
  x <+> (y ::> e) = (x <+> y) ::> e
