{-|
Description : type-level proofs involving contexts
Copyright   : (c) Galois, Inc 2015-2019
Maintainer  : Joe Hendrix <jhendrix@galois.com>

This reflects type level proofs involving contexts.
-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.Ctx.Proofs
  ( leftId
  , assoc
  ) where

import Data.Type.Equality

import Data.Parameterized.Axiom
import Data.Parameterized.Ctx

leftId :: p x -> (EmptyCtx <+> x) :~: x
leftId _ = unsafeAxiom

assoc :: p x -> q y -> r z -> x <+> (y <+> z) :~: (x <+> y) <+> z
assoc _ _ _ = unsafeAxiom
