------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.TraversableFC
-- Copyright        : (c) Galois, Inc 2014-2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Description      : Traversing structures having a single parametric type followed by a fixed kind.
--
-- This module declares classes for working with structures that accept
-- a parametric type parameter followed by some fixed kind.
------------------------------------------------------------------------
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.TraversableFC
  ( TestEqualityFC(..)
  , OrdFC(..)
  , ShowFC(..)
  , HashableFC(..)
  , FunctorFC(..)
  , FoldableFC(..)
  , foldlMFC
  , foldlMFC'
  , foldrMFC
  , foldrMFC'
  , TraversableFC(..)
  , traverseFC_
  , forMFC_
  , forFC_
  , forFC
  , fmapFCDefault
  , foldMapFCDefault
  , allFC
  , anyFC
  , lengthFC
  ) where

import Control.Applicative (Const(..) )
import Control.Monad.Identity ( Identity (..) )
import Data.Coerce
import Data.Kind
import Data.Monoid
import GHC.Exts (build)
import Data.Type.Equality

import Data.Parameterized.Classes

-- | A parameterized type that is a functor on all instances.
--
-- Laws:
--
-- [Identity]    @'fmapFC' 'id' == 'id'@
-- [Composition] @'fmapFC' (f . g) == 'fmapFC' f . 'fmapFC' g@
class FunctorFC (t :: (k -> Type) -> l -> Type) where
  fmapFC :: forall f g. (forall x. f x -> g x) ->
                        (forall x. t f x -> t g x)

-- | A parameterized class for types which can be shown, when given
--   functions to show parameterized subterms.
class ShowFC (t :: (k -> Type) -> l -> Type) where
  {-# MINIMAL showFC | showsPrecFC #-}

  showFC :: forall f. (forall x. f x -> String)
         -> (forall x. t f x -> String)
  showFC sh x = showsPrecFC (\_prec z rest -> sh z ++ rest) 0 x []

  showsPrecFC :: forall f. (forall x. Int -> f x -> ShowS) ->
                           (forall x. Int -> t f x -> ShowS)
  showsPrecFC sh _prec x rest = showFC (\z -> sh 0 z []) x ++ rest


-- | A parameterized class for types which can be hashed, when given
--   functions to hash parameterized subterms.
class HashableFC (t :: (k -> Type) -> l -> Type) where
  hashWithSaltFC :: forall f. (forall x. Int -> f x -> Int) ->
                              (forall x. Int -> t f x -> Int)

-- | A parameterized class for types which can be tested for parameterized equality,
--   when given an equality test for subterms.
class TestEqualityFC (t :: (k -> Type) -> l -> Type) where
  testEqualityFC :: forall f. (forall x y. f x -> f y -> (Maybe (x :~: y))) ->
                              (forall x y. t f x -> t f y -> (Maybe (x :~: y)))

-- | A parameterized class for types which can be tested for parameterized ordering,
--   when given an comparison test for subterms.
class TestEqualityFC t => OrdFC (t :: (k -> Type) -> l -> Type) where
  compareFC :: forall f. (forall x y. f x -> f y -> OrderingF x y) ->
                         (forall x y. t f x -> t f y -> OrderingF x y)

------------------------------------------------------------------------
-- FoldableF

-- | This is a coercion used to avoid overhead associated
-- with function composition.
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce

-- | This is a generalization of the 'Foldable' class to
-- structures over parameterized terms.
class FoldableFC (t :: (k -> Type) -> l -> Type) where
  {-# MINIMAL foldMapFC | foldrFC #-}

  -- | Map each element of the structure to a monoid,
  -- and combine the results.
  foldMapFC :: forall f m. Monoid m => (forall x. f x -> m) -> (forall x. t f x -> m)
  foldMapFC f = foldrFC (mappend . f) mempty

  -- | Right-associative fold of a structure.
  foldrFC :: forall f b. (forall x. f x -> b -> b) -> (forall x. b -> t f x -> b)
  foldrFC f z t = appEndo (foldMapFC (Endo #. f) t) z

  -- | Left-associative fold of a structure.
  foldlFC :: forall f b. (forall x. b -> f x -> b) -> (forall x. b -> t f x -> b)
  foldlFC f z t = appEndo (getDual (foldMapFC (\e -> Dual (Endo (\r -> f r e))) t)) z

  -- | Right-associative fold of a structure,
  -- but with strict application of the operator.
  foldrFC' :: forall f b. (forall x. f x -> b -> b) -> (forall x. b -> t f x -> b)
  foldrFC' f0 z0 xs = foldlFC (f' f0) id xs z0
    where f' f k x z = k $! f x z

  -- | Left-associative fold of a parameterized structure
  -- with a strict accumulator.
  foldlFC' :: forall f b. (forall x. b -> f x -> b) -> (forall x. b -> t f x -> b)
  foldlFC' f0 z0 xs = foldrFC (f' f0) id xs z0
    where f' f x k z = k $! f z x

  -- | Convert structure to list.
  toListFC :: forall f a. (forall x. f x -> a) -> (forall x. t f x -> [a])
  toListFC f t = build (\c n -> foldrFC (\e v -> c (f e) v) n t)

-- | Monadic fold over the elements of a structure from left to right.
foldlMFC :: (FoldableFC t, Monad m) => (forall x . b -> f x -> m b) -> b -> t f c -> m b
foldlMFC f z0 xs = foldrFC f' return xs z0
  where f' x k z = f z x >>= k

-- | Monadic strict fold over the elements of a structure from left to right.
foldlMFC' :: (FoldableFC t, Monad m) => (forall x . b -> f x -> m b) -> b -> t f c -> m b
foldlMFC' f z0 xs = seq z0 $ foldrFC f' return xs z0
  where f' x k z = f z x >>= \r -> seq r (k r)

-- | Monadic fold over the elements of a structure from right to left.
foldrMFC :: (FoldableFC t, Monad m) => (forall x . f x -> b -> m b) -> b -> t f c -> m b
foldrMFC f z0 xs = foldlFC f' return xs z0
  where f' k x z = f x z >>= k

-- | Monadic strict fold over the elements of a structure from right to left.
foldrMFC' :: (FoldableFC t, Monad m) => (forall x . f x -> b -> m b) -> b -> t f c -> m b
foldrMFC' f z0 xs = seq z0 (foldlFC f' return xs z0)
  where f' k x z = f x z >>= \r -> seq r (k r)

-- | Return 'True' if all values satisfy predicate.
allFC :: FoldableFC t => (forall x. f x -> Bool) -> (forall x. t f x -> Bool)
allFC p = getAll #. foldMapFC (All #. p)

-- | Return 'True' if any values satisfy predicate.
anyFC :: FoldableFC t => (forall x. f x -> Bool) -> (forall x. t f x -> Bool)
anyFC p = getAny #. foldMapFC (Any #. p)

-- | Return number of elements that we fold over.
lengthFC :: FoldableFC t => t f x -> Int
lengthFC = foldrFC (const (+1)) 0

------------------------------------------------------------------------
-- TraversableF

class (FunctorFC t, FoldableFC t) => TraversableFC (t :: (k -> Type) -> l -> Type) where
  traverseFC :: forall f g m. Applicative m
             => (forall x. f x -> m (g x))
             -> (forall x. t f x -> m (t g x))

-- | This function may be used as a value for `fmapF` in a `FunctorF`
-- instance.
fmapFCDefault :: TraversableFC t => forall f g. (forall x. f x -> g x) -> (forall x. t f x -> t g x)
fmapFCDefault = \f -> runIdentity . traverseFC (Identity . f)
{-# INLINE fmapFCDefault #-}

-- | This function may be used as a value for `Data.Foldable.foldMap`
-- in a `Foldable` instance.
foldMapFCDefault :: (TraversableFC t, Monoid m) => (forall x. f x -> m) -> (forall x. t f x -> m)
foldMapFCDefault = \f -> getConst . traverseFC (Const . f)
{-# INLINE foldMapFCDefault #-}

-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
traverseFC_ :: (FoldableFC t, Applicative m) => (forall x. f x -> m a) -> (forall x. t f x -> m ())
traverseFC_ f = foldrFC (\e r -> f e *> r) (pure ())
{-# INLINE traverseFC_ #-}

-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
forMFC_ :: (FoldableFC t, Applicative m) => t f c -> (forall x. f x -> m a) -> m ()
forMFC_ v f = traverseFC_ f v
{-# INLINE forMFC_ #-}
{-# DEPRECATED forMFC_ "Use forFC_" #-}

-- | Map each element of a structure to an action, evaluate
-- these actions from left to right, and ignore the results.
forFC_ :: (FoldableFC t, Applicative m) => t f c -> (forall x. f x -> m a) -> m ()
forFC_ v f = traverseFC_ f v
{-# INLINE forFC_ #-}

-- | Flipped 'traverseFC'
forFC ::
  (TraversableFC t, Applicative m) =>
  t f x -> (forall y. f y -> m (g y)) -> m (t g x)
forFC v f = traverseFC f v
{-# INLINE forFC #-}
