{-|
Copyright        : (c) Galois, Inc 2022

See "Data.Parameterized.FinMap".
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Parameterized.FinMap.Safe
  ( FinMap
  -- * Query
  , null
  , lookup
  , size
  -- * Construction
  , incMax
  , embed
  , empty
  , singleton
  , insert
  , buildFinMap
  , append
  , fromVector
  -- * Operations
  , delete
  , decMax
  , mapWithKey
  ) where

import           Prelude hiding (lookup, null)

import           Data.Foldable.WithIndex (FoldableWithIndex(ifoldMap))
import           Data.Functor.WithIndex (FunctorWithIndex(imap))
import           Data.Maybe (isJust)
import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.TypeLits (KnownNat, Nat)

import           Data.Parameterized.Fin (Fin)
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.NatRepr (NatRepr, type (+), type (<=))
import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Vector (Vector)
import qualified Data.Parameterized.Vector as Vec

------------------------------------------------------------------------
-- Type

-- | @'FinMap' n a@ is a map with @'Fin' n@ keys and @a@ values.
data FinMap (n :: Nat) a =
  FinMap
    { getFinMap :: Map (Fin n) a
    , maxSize :: NatRepr n
    }

instance Eq a => Eq (FinMap n a) where
  fm1 == fm2 = getFinMap fm1 == getFinMap fm2
  {-# INLINABLE (==) #-}

instance Functor (FinMap n) where
  fmap f fm = fm { getFinMap = fmap f (getFinMap fm) }
  {-# INLINABLE fmap #-}

instance Foldable (FinMap n) where
  foldMap f = foldMap f . getFinMap
  {-# INLINABLE foldMap #-}

instance Traversable (FinMap n) where
  traverse f fm = FinMap <$> traverse f (getFinMap fm) <*> pure (maxSize fm)

instance FunctorWithIndex (Fin n) (FinMap n) where
  imap f fm = fm { getFinMap = Map.mapWithKey f (getFinMap fm) }
  -- Inline so that RULES for Map.mapWithKey can fire
  {-# INLINE imap #-}

instance FoldableWithIndex (Fin n) (FinMap n) where
  ifoldMap f = Map.foldMapWithKey f . getFinMap
  {-# INLINABLE ifoldMap #-}

-- | Non-lawful instance, provided for testing
instance Show a => Show (FinMap n a) where
  show fm = show (getFinMap fm)
  {-# INLINABLE show #-}

------------------------------------------------------------------------
-- Query

-- | /O(1)/. Is the map empty?
null :: FinMap n a -> Bool
null = Map.null . getFinMap
{-# INLINABLE null #-}

-- | /O(log n)/. Fetch the value at the given key in the map.
lookup :: Fin n -> FinMap n a -> Maybe a
lookup k = Map.lookup k . getFinMap
{-# INLINABLE lookup #-}

-- | /O(nlog(n))/. Number of elements in the map.
--
-- This operation is much slower than 'Data.Parameterized.FinMap.Unsafe.size'
-- because its implementation must provide significant evidence to the
-- type-checker, and the easiest way to do that is fairly inefficient.
-- If speed is a concern, use "Data.Parameterized.FinMap.Unsafe".
size :: forall n a. FinMap n a -> Fin (n + 1)
size fm =
  Fin.countFin (maxSize fm) (\k _count -> isJust (lookup (Fin.mkFin k) fm))

------------------------------------------------------------------------
-- Construction

-- | /O(n log n)/. Increase maximum key/size by 1.
--
-- This does not alter the key-value pairs in the map, but rather increases the
-- maximum number of key-value pairs that the map can hold. See
-- "Data.Parameterized.FinMap" for more information.
--
-- Requires @n + 1 < (maxBound :: Int)@.
incMax :: forall n a. FinMap n a -> FinMap (n + 1) a
incMax fm =
  case NatRepr.leqSucc (Proxy :: Proxy n) of
    NatRepr.LeqProof -> embed (NatRepr.incNat (maxSize fm)) fm

-- | /O(n log n)/. Increase maximum key/size.
--
-- Requires @m < (maxBound :: Int)@.
embed :: (n <= m) => NatRepr m -> FinMap n a -> FinMap m a
embed m fm =
  FinMap
    { getFinMap = Map.mapKeys Fin.embed (getFinMap fm)
    , maxSize = m
    }

-- | /O(1)/. The empty map.
empty :: KnownNat n => FinMap n a
empty = FinMap Map.empty NatRepr.knownNat
{-# INLINABLE empty #-}

-- | /O(1)/. A map with one element.
singleton :: a -> FinMap 1 a
singleton item =
  FinMap
    { getFinMap = Map.singleton (Fin.mkFin (NatRepr.knownNat :: NatRepr 0)) item
    , maxSize = NatRepr.knownNat :: NatRepr 1
    }

-- | /O(log n)/.
insert :: Fin n -> a -> FinMap n a -> FinMap n a
insert k v fm = fm { getFinMap = Map.insert k v (getFinMap fm) }
{-# INLINABLE insert #-}

-- buildFinMap, append, and fromVector are duplicated exactly between the safe
-- and unsafe modules because they are used in comparative testing (and so
-- implementations must be available for both types).

newtype FinMap' a (n :: Nat) = FinMap' { unFinMap' :: FinMap n a }

buildFinMap ::
  forall m a.
  NatRepr m ->
  (forall n. (n + 1 <= m) => NatRepr n -> FinMap n a -> FinMap (n + 1) a) ->
  FinMap m a
buildFinMap m f =
  let f' :: forall k. (k + 1 <= m) => NatRepr k -> FinMap' a k -> FinMap' a (k + 1)
      f' = (\n (FinMap' fin) -> FinMap' (f n fin))
  in unFinMap' (NatRepr.natRecStrictlyBounded m (FinMap' empty) f')

-- | /O(min(n,W))/.
append :: NatRepr n -> a -> FinMap n a -> FinMap (n + 1) a
append k v fm =
  case NatRepr.leqSucc k of
    NatRepr.LeqProof -> insert (Fin.mkFin k) v (incMax fm)

fromVector :: forall n a. Vector n (Maybe a) -> FinMap n a
fromVector v =
  buildFinMap
    (Vec.length v)
    (\k m ->
      case Vec.elemAt k v of
        Just e -> append k e m
        Nothing -> incMax m)

------------------------------------------------------------------------
-- Operations

-- | /O(log n)/.
delete :: Fin n -> FinMap n a -> FinMap n a
delete k fm = fm { getFinMap = Map.delete k (getFinMap fm) }
{-# INLINABLE delete #-}

-- | Decrement the key/size, removing the item at key @n + 1@ if present.
decMax :: NatRepr n -> FinMap (n + 1) a -> FinMap n a
decMax n fm =
  FinMap
    { getFinMap = maybeMapKeys (Fin.tryEmbed sz n) (getFinMap fm)
    , maxSize = n
    }
  where
    sz = maxSize fm

    maybeMapKeys :: Ord k2 => (k1 -> Maybe k2) -> Map k1 a -> Map k2 a
    maybeMapKeys f m =
      Map.foldrWithKey
        (\k v accum ->
           case f k of
             Just k' -> Map.insert k' v accum
             Nothing -> accum)
        Map.empty
        m

mapWithKey :: (Fin n -> a -> b) -> FinMap n a -> FinMap n b
mapWithKey f fm = fm { getFinMap = Map.mapWithKey f (getFinMap fm) }
-- Inline so that RULES for Map.mapWithKey can fire
{-# INLINE mapWithKey #-}
