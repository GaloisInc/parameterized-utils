{-|
Copyright        : (c) Galois, Inc 2014-2015
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This module declares classes for working with types with the kind
@k -> *@ for any kind @k@.  These are generalizations of the
"Data.Functor.Classes" types as they work with any kind @k@, and are
not restricted to '*'.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
#if MIN_VERSION_base(4,9,0)
{-# LANGUAGE Safe #-}
#else
{-# LANGUAGE Trustworthy #-}
#endif
module Data.Parameterized.Classes
  ( -- * Equality exports
    Equality.TestEquality(..)
  , (Equality.:~:)(..)
  , EqF(..)
  , PolyEq(..)
    -- * Ordering generalization
  , OrdF(..)
  , lexCompareF
  , OrderingF(..)
  , joinOrderingF
  , orderingF_refl
  , toOrdering
  , fromOrdering
    -- * Typeclass generalizations
  , ShowF(..)
  , showsF
  , HashableF(..)
  , CoercibleF(..)
    -- * Optics generalizations
  , IndexF
  , IxValueF
  , IxedF(..)
  , IxedF'(..)
  , AtF(..)
    -- * KnownRepr
  , KnownRepr(..)
    -- * Re-exports
  , Data.Maybe.isJust
  ) where

import Data.Functor.Const
import Data.Hashable
import Data.Maybe (isJust)
import Data.Proxy
import Data.Type.Equality as Equality

-- We define these type alias here to avoid importing Control.Lens
-- modules, as this apparently causes problems with the safe Hasekll
-- checking.
type Lens' s a = forall f. Functor f => (a -> f a) -> s -> f s
type Traversal' s a = forall f. Applicative f => (a -> f a) -> s -> f s

------------------------------------------------------------------------
-- CoercibleF

-- | An instance of 'CoercibleF' gives a way to coerce between
--   all the types of a family.  We generally use this to witness
--   the fact that the type parameter to @rtp@ is a phantom type
--   by giving an implementation in terms of Data.Coerce.coerce.
class CoercibleF (rtp :: k -> *) where
  coerceF :: rtp a -> rtp b

instance CoercibleF (Const x) where
  coerceF (Const x) = Const x

------------------------------------------------------------------------
-- EqF

-- | @EqF@ provides a method @eqF@ for testing whether two parameterized
-- types are equal.
--
-- Unlike 'TestEquality', this only works when the type arguments are
-- the same, and does not provide a proof that the types have the same
-- type when they are equal. Thus this can be implemented over
-- parameterized types that are unable to provide evidence that their
-- type arguments are equal.
class EqF (f :: k -> *) where
  eqF :: f a -> f a -> Bool

instance Eq a => EqF (Const a) where
  eqF (Const x) (Const y) = x == y

------------------------------------------------------------------------
-- PolyEq

-- | A polymorphic equality operator that generalizes 'TestEquality'.
class PolyEq u v where
  polyEqF :: u -> v -> Maybe (u :~: v)

  polyEq :: u -> v -> Bool
  polyEq x y = isJust (polyEqF x y)

------------------------------------------------------------------------
-- Ordering

-- | Ordering over two distinct types with a proof they are equal.
data OrderingF x y where
  LTF :: OrderingF x y
  EQF :: OrderingF x x
  GTF :: OrderingF x y

orderingF_refl :: OrderingF x y -> Maybe (x :~: y)
orderingF_refl o =
  case o of
    LTF -> Nothing
    EQF -> Just Refl
    GTF -> Nothing

-- | Convert 'OrderingF' to standard ordering.
toOrdering :: OrderingF x y -> Ordering
toOrdering LTF = LT
toOrdering EQF = EQ
toOrdering GTF = GT

-- | Convert standard ordering to 'OrderingF'.
fromOrdering :: Ordering -> OrderingF x x
fromOrdering LT = LTF
fromOrdering EQ = EQF
fromOrdering GT = GTF

-- | `joinOrderingF x y` first compares on x, returning an equivalent
-- value if it is not `EQF`.  If it is EQF, it returns `y`.
joinOrderingF :: forall (a :: j) (b :: j) (c :: k) (d :: k)
              .  OrderingF a b
              -> (a ~ b => OrderingF c d)
              -> OrderingF c d
joinOrderingF EQF y = y
joinOrderingF LTF _ = LTF
joinOrderingF GTF _ = GTF

------------------------------------------------------------------------
-- OrdF

-- | A parameterized type that can be compared on distinct instances.
class TestEquality ktp => OrdF (ktp :: k -> *) where
  {-# MINIMAL compareF #-}

  -- | compareF compares two keys with different type parameters.
  -- Instances must ensure that keys are only equal if the type
  -- parameters are equal.
  compareF :: ktp x -> ktp y -> OrderingF x y

  leqF :: ktp x -> ktp y -> Bool
  leqF x y =
    case compareF x y of
      LTF -> True
      EQF -> True
      GTF -> False

  ltF :: ktp x -> ktp y -> Bool
  ltF x y =
    case compareF x y of
      LTF -> True
      EQF -> False
      GTF -> False

  geqF :: ktp x -> ktp y -> Bool
  geqF x y =
    case compareF x y of
      LTF -> False
      EQF -> True
      GTF -> True

  gtF :: ktp x -> ktp y -> Bool
  gtF x y =
    case compareF x y of
      LTF -> False
      EQF -> False
      GTF -> True

-- | Compare two values, and if they are equal compare the next values,
-- otherwise return LTF or GTF
lexCompareF :: forall (f :: j -> *) (a :: j) (b :: j) (c :: k) (d :: k)
             .  OrdF f
            => f a
            -> f b
            -> (a ~ b => OrderingF c d)
            -> OrderingF c d
lexCompareF x y = joinOrderingF (compareF x y)

------------------------------------------------------------------------
-- ShowF

-- | A parameterized type that can be shown on all instances.
--
-- To implement @'ShowF' g@, one should implement an instance @'Show'
-- (g tp)@ for all argument types @tp@, then write an empty instance
-- @instance 'ShowF' g@.
class ShowF (f :: k -> *) where
  -- | Provides a show instance for each type.
  withShow :: p f -> q tp -> (Show (f tp) => a) -> a

  default withShow :: Show (f tp) => p f -> q tp -> (Show (f tp) => a) -> a
  withShow _ _ x = x

  showF :: forall tp . f tp -> String
  showF x = withShow (Proxy :: Proxy f) (Proxy :: Proxy tp) (show x)

  -- | Like 'showsPrec', the precedence argument is /one more/ than the
  -- precedence of the enclosing context.
  showsPrecF :: forall tp. Int -> f tp -> String -> String
  showsPrecF p x = withShow (Proxy :: Proxy f) (Proxy :: Proxy tp) (showsPrec p x)

showsF :: ShowF f => f tp -> String -> String
showsF x = showsPrecF 0 x

instance Show x => ShowF (Const x)

------------------------------------------------------------------------
-- IxedF

type family IndexF       (m :: *) :: k -> *
type family IxValueF     (m :: *) :: k -> *

-- | Parameterized generalization of the lens @Ixed@ class.
class IxedF k m where
  -- | Given an index into a container, build a traversal that visits
  --   the given element in the container, if it exists.
  ixF :: forall (x :: k). IndexF m x -> Traversal' m (IxValueF m x)

-- | Parameterized generalization of the lens @Ixed@ class,
--   but with the guarantee that indexes exist in the container.
class IxedF k m => IxedF' k m where
  -- | Given an index into a container, build a lens that
  --   points into the given element in the container.
  ixF' :: forall (x :: k). IndexF m x -> Lens' m (IxValueF m x)

------------------------------------------------------------------------
-- AtF

-- | Parameterized generalization of the lens @At@ class.
class IxedF k m => AtF k m where
  -- | Given an index into a container, build a lens that points into
  --   the given position in the container, whether or not it currently
  --   exists.  Setting values of @atF@ to a @Just@ value will insert
  --   the value if it does not already exist.
  atF :: forall (x :: k). IndexF m x -> Lens' m (Maybe (IxValueF m x))

------------------------------------------------------------------------
-- HashableF

-- | A default salt used in the implementation of 'hash'.
defaultSalt :: Int
#if WORD_SIZE_IN_BITS == 64
defaultSalt = 0xdc36d1615b7400a4
#else
defaultSalt = 0x087fc72c
#endif
{-# INLINE defaultSalt #-}

-- | A parameterized type that is hashable on all instances.
class HashableF (f :: k -> *) where
  hashWithSaltF :: Int -> f tp -> Int

  -- | Hash with default salt.
  hashF :: f tp -> Int
  hashF = hashWithSaltF defaultSalt

instance Hashable a => HashableF (Const a) where
  hashWithSaltF s (Const x) = hashWithSalt s x

------------------------------------------------------------------------
-- KnownRepr

-- | This class is parameterized by a kind @k@ (typically a data
-- kind), a type constructor @f@ of kind @k -> *@ (typically a GADT of
-- singleton types indexed by @k@), and an index parameter @ctx@ of
-- kind @k@.
class KnownRepr (f :: k -> *) (ctx :: k) where
  knownRepr :: f ctx
