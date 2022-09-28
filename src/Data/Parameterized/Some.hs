------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Some
-- Copyright        : (c) Galois, Inc 2014-2019
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Description : a GADT that hides a type parameter
--
-- This module provides 'Some', a GADT that hides a type parameter.
------------------------------------------------------------------------
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Parameterized.Some
  ( Some
  , pattern Some
  , viewSome
  , mapSome
  , traverseSome
  , traverseSome_
  , someLens
  ) where

import Control.Lens (Lens', lens, (&), (^.), (.~))
import Data.Hashable
import Data.Parameterized.Classes
import Data.Parameterized.TraversableF
import qualified Data.Some as Some

-- This used to be a @data@ type, but is now a newtype around Some.Some. The
-- idea is that Some.Some provides an (internally unsafe) newtype-based encoding
-- which has better performance characteristics, see the upstream documentation.
newtype Some f = MkSome (Some.Some f)

-- | See instances for 'Some.Some'.
deriving instance Applicative f => Semigroup (Some f)
-- | See instances for 'Some.Some'.
deriving instance Applicative f => Monoid (Some f)

{-# COMPLETE Some #-}
pattern Some :: f a -> Some f
pattern Some x <- MkSome (Some.Some x)
  where Some x = MkSome (Some.Some x)

instance TestEquality f => Eq (Some f) where
  Some x == Some y = isJust (testEquality x y)

instance OrdF f => Ord (Some f) where
  compare (Some x) (Some y) = toOrdering (compareF x y)

instance (HashableF f, TestEquality f) => Hashable (Some f) where
  hashWithSalt s (Some x) = hashWithSaltF s x
  hash (Some x) = hashF x

instance ShowF f => Show (Some f) where
  show (Some x) = showF x

-- | Project out of Some.
viewSome :: (forall tp . f tp -> r) -> Some f -> r
viewSome f (Some x) = f x

-- | Apply function to inner value.
mapSome :: (forall tp . f tp -> g tp) -> Some f -> Some g
mapSome f (Some x) = Some $! f x

{-# INLINE traverseSome #-}
-- | Modify the inner value.
traverseSome :: Functor m
             => (forall tp . f tp -> m (g tp))
             -> Some f
             -> m (Some g)
traverseSome f (Some x) = Some `fmap` f x

{-# INLINE traverseSome_ #-}
-- | Modify the inner value.
traverseSome_ :: Functor m => (forall tp . f tp -> m ()) -> Some f -> m ()
traverseSome_ f (Some x) = (\_ -> ()) `fmap` f x

instance FunctorF     Some where fmapF     = mapSome
instance FoldableF    Some where foldMapF  = foldMapFDefault
instance TraversableF Some where traverseF = traverseSome

-- | A lens that is polymorphic in the index may be used on a value with an
-- existentially-quantified index.
someLens :: (forall tp. Lens' (f tp) a) -> Lens' (Some f) a
someLens l = lens (\(Some x) -> x ^. l) (\(Some x) v -> Some (x & l .~ v))
