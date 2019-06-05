------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.TraversableF
-- Copyright        : (c) Galois, Inc 2014-2019
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Description      : Traversing structures having a single parametric type
--
-- This module declares classes for working with structures that accept
-- a single parametric type parameter.
------------------------------------------------------------------------
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
module Data.Parameterized.TraversableF
  ( FunctorF(..)
  , FoldableF(..)
  , foldlMF
  , foldrMF
  , TraversableF(..)
  , traverseF_
  , forMFC_
  , fmapFDefault
  , foldMapFDefault
  , allF
  , anyF
  , lengthF
  ) where

import Control.Applicative
import Control.Monad.Identity
import Data.Coerce
import Data.Functor.Compose (Compose(..))
import Data.Monoid
import GHC.Exts (build)

import Data.Parameterized.TraversableFC

-- | A parameterized type that is a functor on all instances.
class FunctorF m where
  fmapF :: (forall x . f x -> g x) -> m f -> m g

instance FunctorF (Const x) where
  fmapF _ = coerce

------------------------------------------------------------------------
-- FoldableF

-- | This is a coercion used to avoid overhead associated
-- with function composition.
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce

-- | This is a generalization of the 'Foldable' class to
-- structures over parameterized terms.
class FoldableF (t :: (k -> *) -> *) where
  {-# MINIMAL foldMapF | foldrF #-}

  -- | Map each element of the structure to a monoid,
  -- and combine the results.
  foldMapF :: Monoid m => (forall s . e s -> m) -> t e -> m
  foldMapF f = foldrF (mappend . f) mempty

  -- | Right-associative fold of a structure.
  foldrF :: (forall s . e s -> b -> b) -> b -> t e -> b
  foldrF f z t = appEndo (foldMapF (Endo #. f) t) z

  -- | Left-associative fold of a structure.
  foldlF :: (forall s . b -> e s -> b) -> b -> t e -> b
  foldlF f z t = appEndo (getDual (foldMapF (\e -> Dual (Endo (\r -> f r e))) t)) z

  -- | Right-associative fold of a structure,
  -- but with strict application of the operator.
  foldrF' :: (forall s . e s -> b -> b) -> b -> t e -> b
  foldrF' f0 z0 xs = foldlF (f' f0) id xs z0
    where f' f k x z = k $! f x z

  -- | Left-associative fold of a parameterized structure
  -- with a strict accumulator.
  foldlF' :: (forall s . b -> e s -> b) -> b -> t e -> b
  foldlF' f0 z0 xs = foldrF (f' f0) id xs z0
    where f' f x k z = k $! f z x

  -- | Convert structure to list.
  toListF :: (forall tp . f tp -> a) -> t f -> [a]
  toListF f t = build (\c n -> foldrF (\e v -> c (f e) v) n t)

-- | Monadic fold over the elements of a structure from left to right.
foldlMF :: (FoldableF t, Monad m) => (forall x . b -> f x -> m b) -> b -> t f -> m b
foldlMF f z0 xs = foldrF f' return xs z0
  where f' x k z = f z x >>= k

-- | Monadic fold over the elements of a structure from right to left.
foldrMF :: (FoldableF t, Monad m) => (forall x . f x -> b -> m b) -> b -> t f -> m b
foldrMF f z0 xs = foldlF f' return xs z0
  where f' k x z = f x z >>= k

-- | Return 'True' if all values satisfy the predicate.
allF :: FoldableF t => (forall tp . f tp -> Bool) -> t f -> Bool
allF p = getAll #. foldMapF (All #. p)

-- | Return 'True' if any values satisfy the predicate.
anyF :: FoldableF t => (forall tp . f tp -> Bool) -> t f -> Bool
anyF p = getAny #. foldMapF (Any #. p)

-- | Return number of elements that we fold over.
lengthF :: FoldableF t => t f -> Int
lengthF = foldrF (const (+1)) 0

instance FoldableF (Const x) where
  foldMapF _ _ = mempty

------------------------------------------------------------------------
-- TraversableF

class (FunctorF t, FoldableF t) => TraversableF t where
  traverseF :: Applicative m
            => (forall s . e s -> m (f s))
            -> t e
            -> m (t f)

instance TraversableF (Const x) where
  traverseF _ (Const x) = pure (Const x)

-- | This function may be used as a value for `fmapF` in a `FunctorF`
-- instance.
fmapFDefault :: TraversableF t => (forall s . e s -> f s) -> t e -> t f
fmapFDefault f = runIdentity #. traverseF (Identity #. f)
{-# INLINE fmapFDefault #-}

-- | This function may be used as a value for `Data.Foldable.foldMap`
-- in a `Foldable` instance.
foldMapFDefault :: (TraversableF t, Monoid m) => (forall s . e s -> m) -> t e -> m
foldMapFDefault f = getConst #. traverseF (Const #. f)

-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
traverseF_ :: (FoldableF t, Applicative f) => (forall s . e s  -> f a) -> t e -> f ()
traverseF_ f = foldrF (\e r -> f e *> r) (pure ())


-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
forMF_ :: (FoldableF t, Applicative m) => t f -> (forall x. f x -> m a) -> m ()
forMF_ v f = traverseF_ f v
{-# INLINE forMF_ #-}

------------------------------------------------------------------------
-- TraversableF (Compose s t)

instance ( FunctorF (s :: (k -> *) -> *)
         , FunctorFC (t :: (l -> *) -> (k -> *))
         ) =>
         FunctorF (Compose s t) where
  fmapF f (Compose v) = Compose $ fmapF (fmapFC f) v

instance ( TraversableF (s :: (k -> *) -> *)
         , TraversableFC (t :: (l -> *) -> (k -> *))
         ) =>
         FoldableF (Compose s t) where
  foldMapF = foldMapFDefault

-- | Traverse twice over: go under the @t@, under the @s@ and lift @m@ out.
instance ( TraversableF (s :: (k -> *) -> *)
         , TraversableFC (t :: (l -> *) -> (k -> *))
         ) =>
         TraversableF (Compose s t) where
  traverseF :: forall (f :: l -> *) (g :: l -> *) m. (Applicative m) =>
               (forall (u :: l). f u -> m (g u))
            -> Compose s t f -> m (Compose s t g)
  traverseF f (Compose v) = Compose <$> traverseF (traverseFC f) v
