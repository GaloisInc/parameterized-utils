{-|
Copyright        : (c) Galois, Inc 2022

See "Data.Parameterized.FinMap".
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
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
  , empty
  , singleton
  , insert
  , append
  , fromVector
  -- * Operations
  , delete
  , decMax
  ) where

import           Prelude hiding (lookup, null)

import           Data.Proxy (Proxy(Proxy))
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.Types (Nat)

import           Data.Parameterized.Fin (Fin)
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.NatRepr (NatRepr, type (+))
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
  sm1 == sm2 = getFinMap sm1 == getFinMap sm2

-- | Non-lawful instance, provided for testing
instance Show a => Show (FinMap n a) where
  show sm = show (getFinMap sm)

------------------------------------------------------------------------
-- Query

-- | /O(1)/. Is the map empty?
null :: FinMap n a -> Bool
null = Map.null . getFinMap

lookup :: Fin n -> FinMap n a -> Maybe a
lookup k = Map.lookup k . getFinMap

newtype Fin' n = Fin' { getFin' :: Fin (n + 1) }

-- | /O(nlog(n))/. Number of elements in the map.
size :: forall n a. FinMap n a -> Fin (n + 1)
size sm =
  getFin' $
    NatRepr.natRecStrictlyBounded
      (maxSize sm)
      (Fin' Fin.minFin)
      (\(k :: NatRepr m) (Fin' count) ->
        Fin' $
          case lookup (Fin.mkFin k) sm of
            Just _ -> Fin.incFin count
            Nothing ->
              case NatRepr.leqSucc count of
                NatRepr.LeqProof -> Fin.embed count)

------------------------------------------------------------------------
-- Construction

-- | /O(1)/. Increase maximum key/size.
--
-- Requires @n + 1 < (maxBound :: Int)@.
incMax :: forall n a. FinMap n a -> FinMap (n + 1) a
incMax sm =
  FinMap
    { getFinMap =
      case NatRepr.leqSucc (Proxy :: Proxy n) of
        NatRepr.LeqProof -> Map.mapKeys Fin.embed (getFinMap sm)
    , maxSize = NatRepr.incNat (maxSize sm)
    }

-- | /O(1)/. The empty map.
empty :: FinMap 0 a
empty = FinMap Map.empty (NatRepr.knownNat :: NatRepr 0)

-- | /O(1)/. A map with one element.
singleton :: a -> FinMap 1 a
singleton item =
  FinMap
    { getFinMap = Map.singleton (Fin.mkFin (NatRepr.knownNat :: NatRepr 0)) item
    , maxSize = NatRepr.knownNat :: NatRepr 1
    }

-- | /O(log n)/.
insert :: Fin n -> a -> FinMap n a -> FinMap n a
insert k v sm = sm { getFinMap = Map.insert k v (getFinMap sm) }

newtype FlipMap a n = FlipMap { unFlipMap :: FinMap n a }

-- append and fromVector are duplicated exactly between the safe and unsafe
-- modules because they are used in comparative testing (and so implementations
-- must be available for both types).

-- | /O(log n)/.
append :: NatRepr n -> a -> FinMap n a -> FinMap (n + 1) a
append k v sm =
  case NatRepr.leqSucc k of
    NatRepr.LeqProof -> insert (Fin.mkFin k) v (incMax sm)

fromVector :: forall n a. Vector n a -> FinMap n a
fromVector v =
  unFlipMap $
    NatRepr.natRecStrictlyBounded
    len
    (FlipMap empty)
    (\k (FlipMap m) -> FlipMap (append k (Vec.elemAt k v) m))
  where len = Vec.length v

------------------------------------------------------------------------
-- Operations

-- | /O(log n)/.
delete :: Fin n -> FinMap n a -> FinMap n a
delete k sm = sm { getFinMap = Map.delete k (getFinMap sm) }

-- | Decrement the key/size, removing the item at key @n + 1@ if present.
decMax :: NatRepr n -> FinMap (n + 1) a -> FinMap n a
decMax n sm =
  FinMap
    { getFinMap = maybeMapKeys (Fin.tryEmbed sz n) (getFinMap sm)
    , maxSize = n
    }
  where
    sz = maxSize sm

    maybeMapKeys :: Ord k2 => (k1 -> Maybe k2) -> Map k1 a -> Map k2 a
    maybeMapKeys f m =
      Map.foldrWithKey
        (\k v accum ->
           case f k of
             Just k' -> Map.insert k' v accum
             Nothing -> accum)
        Map.empty
        m
