{-|
Description : Classes for working with type of kind @(k -> *) -> *@
Copyright   : (c) Galois, Inc 2014-2019
Maintainer  : Langston Barrett <langston@galois.com>

This module declares classes for working with types with the kind
@(k -> *) -> *@ for any kind @k@.

These classes generally require type-level evidence for operations
on their subterms, but don't actually provide it themselves (because
their types are not themselves parameterized, unlike those in
"Data.Parameterized.TraversableFC").

Note that there is still some ambiguity around naming conventions, see
<https://github.com/GaloisInc/parameterized-utils/issues/23 issue 23>.
-}

{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeOperators #-}

-- See https://github.com/GaloisInc/parameterized-utils/issues/149
{-# OPTIONS_GHC -Wno-trustworthy-safe #-}

module Data.Parameterized.ClassesC
  ( TestEqualityC(..)
  , OrdC(..)
  ) where

import Data.Type.Equality ((:~:)(..))
import Data.Kind
import Data.Maybe (isJust)
import Data.Parameterized.Classes (OrderingF, toOrdering)
import Data.Parameterized.Some (Some(..))

class TestEqualityC (t :: (k -> Type) -> Type) where
  testEqualityC :: (forall x y. f x -> f y -> Maybe (x :~: y))
                -> t f
                -> t f
                -> Bool

class TestEqualityC t => OrdC (t :: (k -> Type) -> Type) where
  compareC :: (forall x y. f x -> g y -> OrderingF x y)
           -> t f
           -> t g
           -> Ordering

-- | This instance demonstrates where the above class is useful: namely, in
-- types with existential quantification.
instance TestEqualityC Some where
  testEqualityC subterms (Some someone) (Some something) =
    isJust (subterms someone something)

instance OrdC Some where
  compareC subterms (Some someone) (Some something) =
    toOrdering (subterms someone something)
