{-|
Copyright        : (c) Galois, Inc 2014-2015
Maintainer       : Langston Barrett <langston@galois.com>

This module declares classes for working with types with the kind
@(k -> *) -> *@ for any kind @k@.

These classes generally require type-level evidence for operations
on their subterms, but don't actually provide it themselves (because
their types are not themselves parameterized, unlike those in
"Data.Parameterized.TraverableFC").

Note that there is still some ambiguity around naming conventions, see
<https://github.com/GaloisInc/parameterized-utils/issues/23 issue 23>.
-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}

module Data.Parameterized.ClassesC
  ( TestEqualityC(..)
  , OrdC(..)
  ) where

import Data.Type.Equality ((:~:)(..))
import Data.Parameterized.Classes (OrderingF)

class TestEqualityC (t :: (k -> *) -> *) where
  testEqualityC :: (forall x y. f x -> f y -> Maybe (x :~: y)) -- ^ Equality of subterm types
                -> t f
                -> t f
                -> Bool

class TestEqualityC t => OrdC (t :: (k -> *) -> *) where
  compareC :: (forall x. f x -> g x -> OrderingF f g) -- ^ Ordering of subterm types
           -> t f
           -> t g
           -> Ordering
