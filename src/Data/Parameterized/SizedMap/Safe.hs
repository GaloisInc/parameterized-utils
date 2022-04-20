{-|
Copyright        : (c) Galois, Inc 2022

See "Data.Parameterized.SizedMap".
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Parameterized.SizedMap.Safe
  ( SizedMap
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

-- | @'SizedMap' n a@ is a map with 'NatRepr' keys, @a@ values, and keys all
-- less than @n@ (and so, size up to @n@).
data SizedMap (n :: Nat) a =
  SizedMap
    { getSizedMap :: Map (Fin n) a
    , maxSize :: NatRepr n
    }

instance Eq a => Eq (SizedMap n a) where
  sm1 == sm2 = getSizedMap sm1 == getSizedMap sm2

-- | Non-lawful instance, provided for testing
instance Show a => Show (SizedMap n a) where
  show sm = show (getSizedMap sm)

------------------------------------------------------------------------
-- Query

-- | /O(1)/. Is the map empty?
null :: SizedMap n a -> Bool
null = Map.null . getSizedMap

lookup :: Fin n -> SizedMap n a -> Maybe a
lookup k = Map.lookup k . getSizedMap

newtype Fin' n = Fin' { getFin' :: Fin (n + 1) }

-- | /O(nlog(n))/. Number of elements in the map.
size :: forall n a. SizedMap n a -> Fin (n + 1)
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
incMax :: forall n a. SizedMap n a -> SizedMap (n + 1) a
incMax sm =
  SizedMap
    { getSizedMap =
      case NatRepr.leqSucc (Proxy :: Proxy n) of
        NatRepr.LeqProof -> Map.mapKeys Fin.embed (getSizedMap sm)
    , maxSize = NatRepr.incNat (maxSize sm)
    }

-- | /O(1)/. The empty map.
empty :: SizedMap 0 a
empty = SizedMap Map.empty (NatRepr.knownNat :: NatRepr 0)

-- | /O(1)/. A map with one element.
singleton :: a -> SizedMap 1 a
singleton item =
  SizedMap
    { getSizedMap = Map.singleton (Fin.mkFin (NatRepr.knownNat :: NatRepr 0)) item
    , maxSize = NatRepr.knownNat :: NatRepr 1
    }

-- | /O(log n)/.
insert :: Fin n -> a -> SizedMap n a -> SizedMap n a
insert k v sm = sm { getSizedMap = Map.insert k v (getSizedMap sm) }

newtype FlipMap a n = FlipMap { unFlipMap :: SizedMap n a }

-- append and fromVector are duplicated exactly between the safe and unsafe
-- modules because they are used in comparative testing (and so implementations
-- must be available for both types).

-- | /O(log n)/.
append :: NatRepr n -> a -> SizedMap n a -> SizedMap (n + 1) a
append k v sm =
  case NatRepr.leqSucc k of
    NatRepr.LeqProof -> insert (Fin.mkFin k) v (incMax sm)

fromVector :: forall n a. Vector n a -> SizedMap n a
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
delete :: Fin n -> SizedMap n a -> SizedMap n a
delete k sm = sm { getSizedMap = Map.delete k (getSizedMap sm) }

-- | Decrement the key/size, removing the item at key @n + 1@ if present.
decMax :: NatRepr n -> SizedMap (n + 1) a -> SizedMap n a
decMax n sm =
  SizedMap
    { getSizedMap = maybeMapKeys (Fin.tryEmbed sz n) (getSizedMap sm)
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
