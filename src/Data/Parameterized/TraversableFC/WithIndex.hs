------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.TraversableFC.WithIndex
-- Copyright        : (c) Galois, Inc 2021
-- Maintainer       : Langston Barrett
-- Description      : 'TraversableFC' classes, but with indices.
--
-- As in the package indexed-traversable.
------------------------------------------------------------------------
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Parameterized.TraversableFC.WithIndex
  ( FunctorFCWithIndex(..)
  , FoldableFCWithIndex(..)
  , ifoldlMFC
  , ifoldrMFC
  , iallFC
  , ianyFC
  , TraversableFCWithIndex(..)
  , imapFCDefault
  , ifoldMapFCDefault
  ) where

import Data.Functor.Const (Const(Const, getConst))
import Data.Functor.Identity (Identity(Identity, runIdentity))
import Data.Kind
import Data.Monoid (All(..), Any(..), Endo(Endo), appEndo, Dual(Dual, getDual))
import Data.Profunctor.Unsafe ((#.))
import GHC.Exts (build)

import Data.Parameterized.Classes
import Data.Parameterized.TraversableFC

class FunctorFC t => FunctorFCWithIndex (t :: (k -> Type) -> l -> Type) where
  -- | Like 'fmapFC', but with an index.
  --
  -- @
  -- 'fmapFC' f ≡ 'imapFC' ('const' f)
  -- @
  imapFC ::
    forall f g z.
    (forall x. IndexF (t f z) x -> f x -> g x)
    -> t f z
    -> t g z

------------------------------------------------------------------------

class (FoldableFC t, FunctorFCWithIndex t) => FoldableFCWithIndex (t :: (k -> Type) -> l -> Type) where

  -- | Like 'foldMapFC', but with an index.
  --
  -- @
  -- 'foldMapFC' f ≡ 'ifoldMapFC' ('const' f)
  -- @
  ifoldMapFC ::
    forall f m z.
    Monoid m =>
    (forall x. IndexF (t f z) x -> f x -> m) ->
    t f z ->
    m
  ifoldMapFC f = ifoldrFC (\i x -> mappend (f i x)) mempty

  -- | Like 'foldrFC', but with an index.
  ifoldrFC ::
    forall z f b.
    (forall x. IndexF (t f z) x -> f x -> b -> b) ->
    b ->
    t f z ->
    b
  ifoldrFC f z t = appEndo (ifoldMapFC (\i x -> Endo (f i x)) t) z

  -- | Like 'foldlFC', but with an index.
  ifoldlFC ::
    forall f b z.
    (forall x. IndexF (t f z) x -> b -> f x -> b) ->
    b ->
    t f z ->
    b
  ifoldlFC f z t =
    appEndo (getDual (ifoldMapFC (\i e -> Dual (Endo (\r -> f i r e))) t)) z

  -- | Like 'ifoldrFC', but with an index.
  ifoldrFC' ::
    forall f b z.
    (forall x. IndexF (t f z) x -> f x -> b -> b) ->
    b ->
    t f z ->
    b
  ifoldrFC' f0 z0 xs = ifoldlFC (f' f0) id xs z0
    where f' f i k x z = k $! f i x z

  -- | Like 'ifoldlFC', but with an index.
  ifoldlFC' :: forall f b. (forall x. b -> f x -> b) -> (forall x. b -> t f x -> b)
  ifoldlFC' f0 z0 xs = foldrFC (f' f0) id xs z0
    where f' f x k z = k $! f z x

  -- | Convert structure to list.
  itoListFC ::
    forall f a z.
    (forall x. IndexF (t f z) x -> f x -> a) ->
    t f z ->
    [a]
  itoListFC f t = build (\c n -> ifoldrFC (\i e v -> c (f i e) v) n t)

-- | Like 'foldlMFC', but with an index.
ifoldlMFC ::
  FoldableFCWithIndex t =>
  Monad m =>
  (forall x. IndexF (t f z) x -> b -> f x -> m b) ->
  b ->
  t f z ->
  m b
ifoldlMFC f z0 xs = ifoldlFC (\i k x z -> f i z x >>= k) return xs z0

-- | Like 'foldrMFC', but with an index.
ifoldrMFC ::
  FoldableFCWithIndex t =>
  Monad m =>
  (forall x. IndexF (t f z) x -> f x -> b -> m b) ->
  b ->
  t f z ->
  m b
ifoldrMFC f z0 xs = ifoldlFC (\i k x z -> f i x z >>= k) return xs z0

-- | Like 'allFC', but with an index.
iallFC ::
  FoldableFCWithIndex t =>
  (forall x. IndexF (t f z) x -> f x -> Bool) ->
  t f z ->
  Bool
iallFC p = getAll #. ifoldMapFC (\i x -> All (p i x))

-- | Like 'anyFC', but with an index.
ianyFC ::
  FoldableFCWithIndex t =>
  (forall x. IndexF (t f z) x -> f x -> Bool) ->
  t f z -> Bool
ianyFC p = getAny #. ifoldMapFC (\i x -> Any (p i x))

------------------------------------------------------------------------

class (TraversableFC t, FoldableFCWithIndex t) => TraversableFCWithIndex (t :: (k -> Type) -> l -> Type) where
  -- | Like 'traverseFC', but with an index.
  --
  -- @
  -- 'traverseFC' f ≡ 'itraverseFC' ('const' f)
  -- @
  itraverseFC ::
    forall m z f g.
    Applicative m =>
    (forall x. IndexF (t f z) x -> f x -> m (g x)) ->
    t f z ->
    m (t g z)

imapFCDefault ::
  forall t f g z.
  TraversableFCWithIndex t =>
  (forall x. IndexF (t f z) x -> f x -> g x)
  -> t f z
  -> t g z
imapFCDefault f = runIdentity #. itraverseFC (\i x -> Identity (f i x))
{-# INLINEABLE imapFCDefault #-}

ifoldMapFCDefault ::
  forall t m z f.
  TraversableFCWithIndex t =>
  Monoid m =>
  (forall x. IndexF (t f z) x -> f x -> m) ->
  t f z ->
  m
ifoldMapFCDefault f = getConst #. itraverseFC (\i x -> Const (f i x))
{-# INLINEABLE ifoldMapFCDefault #-}
