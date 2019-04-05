{-|
Description      : Type-level lists.
Copyright        : (c) Galois, Inc 2015-2019
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module defines type-level lists used for representing the type of
variables in a context.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Safe #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Parameterized.Ctx
  ( type Ctx(..)
  , EmptyCtx
  , SingleCtx
  , (::>)
  , type (<+>)

    -- * Type context manipulation
  , CtxSize
  , CtxLookup
  , CtxUpdate
  , CtxLookupRight
  , CtxUpdateRight
  , CheckIx
  , ValidIx
  , FromLeft
  ) where

import Data.Kind (Constraint)
import GHC.TypeLits (Nat, type (+), type (-), type (<=?), TypeError, ErrorMessage(..))

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


-- | This type family computes the number of elements in a 'Ctx'
type family CtxSize (a :: Ctx k) :: Nat where
  CtxSize 'EmptyCtx   = 0
  CtxSize (xs '::> x) = 1 + CtxSize xs

-- | Helper type family used to generate descriptive error messages when
-- an index is larger than the length of the 'Ctx' being indexed.
type family CheckIx (ctx :: Ctx k) (n :: Nat) (b :: Bool) :: Constraint where
  CheckIx ctx n 'True = ()
  CheckIx ctx n 'False = TypeError ('Text "Index "            ':<>: 'ShowType n
                              ':<>: 'Text " out of range in " ':<>: 'ShowType ctx)

-- | A constraint that checks that the nat @n@ is a valid index into the
--   context @ctx@, and raises a type error if not.
type ValidIx (n :: Nat) (ctx :: Ctx k)
  = CheckIx ctx n (n+1 <=? CtxSize ctx)

-- | 'Ctx' is a snoc-list. In order to use the more intuitive left-to-right
-- ordering of elements the desired index is subtracted from the total
-- number of elements.
type FromLeft ctx n = CtxSize ctx - 1 - n

-- | Lookup the value in a context by number, from the right
type family CtxLookupRight (n :: Nat) (ctx :: Ctx k) :: k where
  CtxLookupRight 0 (ctx '::> r) = r
  CtxLookupRight n (ctx '::> r) = CtxLookupRight (n-1) ctx

-- | Update the value in a context by number, from the right.  If the index
--   is out of range, the context is unchanged.
type family CtxUpdateRight (n :: Nat) (x::k) (ctx :: Ctx k) :: Ctx k where
  CtxUpdateRight n x 'EmptyCtx      = 'EmptyCtx
  CtxUpdateRight 0 x (ctx '::> old) = ctx '::> x
  CtxUpdateRight n x (ctx '::> y)   = CtxUpdateRight (n-1) x ctx '::> y

-- | Lookup the value in a context by number, from the left.
--   Produce a type error if the index is out of range.
type CtxLookup (n :: Nat) (ctx :: Ctx k)
  = CtxLookupRight (FromLeft ctx n) ctx

-- | Update the value in a context by number, from the left.  If the index
--   is out of range, the context is unchanged.
type CtxUpdate (n :: Nat) (x :: k) (ctx :: Ctx k)
  = CtxUpdateRight (FromLeft ctx n) x ctx
