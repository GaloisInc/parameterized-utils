------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.TraversableFC
-- Copyright        : (c) Galois, Inc 2014-2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- This module declares classes for working with structures that accept
-- a parametric type parameter followed by some fixed kind.
------------------------------------------------------------------------
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
module Data.Parameterized.TraversableFC
  ( FunctorFC(..)
  , FoldableFC(..)
  , TraversableFC(..)
  , traverseFC_
  , forMFC_
  , fmapFCDefault
  , foldMapFCDefault
  ) where

import Control.Applicative
import Control.Monad.Identity
import Data.Coerce
import Data.Monoid
import GHC.Exts (build)

-- | A parameterized type that is a function on all instances.
class FunctorFC m where
  fmapFC :: (forall x . f x -> g x) -> m f tp -> m g tp

------------------------------------------------------------------------
-- FoldableF

-- | This is a coercision used to avoid overhead associated
-- with function composition.
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce

-- | This is a generalization of the @Foldable@ class to
-- structures over parameterized terms.
class FunctorFC t => FoldableFC (t :: (k -> *) -> l -> *) where
  {-# MINIMAL foldMapFC | foldrFC #-}

  -- | Map each element of the structure to a monoid,
  -- and combine the results.
  foldMapFC :: Monoid m => (forall s . e s -> m) -> t e c -> m
  foldMapFC f = foldrFC (mappend . f) mempty

  -- | Right-associative fold of a structure.
  foldrFC :: (forall s . e s -> b -> b) -> b -> t e c -> b
  foldrFC f z t = appEndo (foldMapFC (Endo #. f) t) z

  -- | Left-associative fold of a structure.
  foldlFC :: (forall s . b -> e s -> b) -> b -> t e c -> b
  foldlFC f z t = appEndo (getDual (foldMapFC (\e -> Dual (Endo (\r -> f r e))) t)) z

  -- | Right-associative fold of a structure,
  -- but with strict application of the operator.
  foldrFC' :: (forall s . e s -> b -> b) -> b -> t e c -> b
  foldrFC' f0 z0 xs = foldlFC (f' f0) id xs z0
    where f' f k x z = k $! f x z

  -- | Left-associative fold of a parameterized structure
  -- with a strict accumulator.
  foldlFC' :: (forall s . b -> e s -> b) -> b -> t e c -> b
  foldlFC' f0 z0 xs = foldrFC (f' f0) id xs z0
    where f' f x k z = k $! f z x

  -- | Convert structure to list.
  toListFC :: (forall tp . f tp -> a) -> t f c -> [a]
  toListFC f t = build (\c n -> foldrFC (\e v -> c (f e) v) n t)

------------------------------------------------------------------------
-- TraversableF

class FoldableFC t => TraversableFC t where
  traverseFC :: Applicative m
             => (forall s . e s -> m (f s))
             -> t e c
             -> m (t f c)

-- | This function may be used as a value for `fmapF` in a `FunctorF`
-- instance.
fmapFCDefault :: TraversableFC t => (forall s . e s -> f s) -> t e c -> t f c
fmapFCDefault = \f -> runIdentity . traverseFC (Identity . f)
{-# INLINE fmapFCDefault #-}

-- | This function may be used as a value for `Data.Foldable.foldMap`
-- in a `Foldable` instance.
foldMapFCDefault :: (TraversableFC t, Monoid m) => (forall s . e s -> m) -> t e c -> m
foldMapFCDefault = \f -> getConst . traverseFC (Const . f)
{-# INLINE foldMapFCDefault #-}

-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
traverseFC_ :: (FoldableFC t, Applicative f) => (forall s . e s  -> f ()) -> t e c -> f ()
traverseFC_ f = foldrFC (\e r -> f e *> r) (pure ())
{-# INLINE traverseFC_ #-}

-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
forMFC_ :: (FoldableFC t, Applicative f) => t e c -> (forall s . e s  -> f ()) -> f ()
forMFC_ v f = traverseFC_ f v
{-# INLINE forMFC_ #-}
