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

module Data.Parameterized.FinMap.Unsafe
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

import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           GHC.Types (Nat)
import           Numeric.Natural (Natural)
import           Unsafe.Coerce (unsafeCoerce)

import           Data.Parameterized.Fin (Fin, mkFin)
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.NatRepr (LeqProof, NatRepr, type (+))
import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.Vector (Vector)
import qualified Data.Parameterized.Vector as Vec

------------------------------------------------------------------------
-- Type

-- This datatype has two important invariants:
--
-- * Its keys must be less than the nat in its type.
-- * Its size must be less than the maximum Int.
--
-- If this invariant holds, all of the unsafe operations in this module
-- (fromJust, unsafeCoerce) will work as intended.

-- | @'FinMap' n a@ is a map with 'NatRepr' keys, @a@ values, and keys all
-- less than @n@ (and so, size up to @n@).
newtype FinMap (n :: Nat) a = FinMap { getFinMap :: IntMap a }

instance Eq a => Eq (FinMap n a) where
  sm1 == sm2 = getFinMap sm1 == getFinMap sm2

-- | Non-lawful instance, provided for testing
instance Show a => Show (FinMap n a) where
  show sm = show (getFinMap sm)

------------------------------------------------------------------------
-- Query

-- | /O(1)/. Is the map empty?
null :: FinMap n a -> Bool
null = IntMap.null . getFinMap
{-# INLINABLE null #-}

-- | /O(min(n,W))/. Get the value at the given key in the map.
lookup :: Fin n -> FinMap n a -> Maybe a
lookup k = IntMap.lookup (fromIntegral (Fin.finToNat k)) . getFinMap

-- This is pulled out as a function so that it's obvious that its use is safe
-- (since Natural is unbounded), whereas other uses of fromIntegral require more
-- careful reasoning.
intToNat :: Int -> Natural
intToNat = fromIntegral
{-# INLINE intToNat #-}

-- | /O(n)/. Number of elements in the map.
size :: forall n a. FinMap n a -> Fin (n + 1)
size sm =
  case NatRepr.mkNatRepr (intToNat (IntMap.size (getFinMap sm))) of
    Some (repr :: NatRepr m) ->
      case unsafeCoerce (NatRepr.LeqProof :: LeqProof 0 0) :: LeqProof (m + 1) (n + 1) of
        NatRepr.LeqProof -> mkFin @m @(n + 1) repr

------------------------------------------------------------------------
-- Construction

-- | /O(1)/. Increase maximum key/size.
--
-- Requires @n + 1 < (maxBound :: Int)@.
incMax :: FinMap n a -> FinMap (n + 1) a
incMax = FinMap . getFinMap
{-# INLINE incMax #-}

-- | /O(1)/. The empty map.
empty :: FinMap 0 a
empty = FinMap IntMap.empty
{-# INLINE empty #-}

-- | /O(1)/. A map with one element.
singleton :: a -> FinMap 1 a
singleton = FinMap . IntMap.singleton 0
{-# INLINABLE singleton #-}

-- | /O(min(n,W))/.
insert :: Fin n -> a -> FinMap n a -> FinMap n a
insert k v sm =
  FinMap (IntMap.insert (fromIntegral (Fin.finToNat k)) v (getFinMap sm))

newtype FlipMap a n = FlipMap { unFlipMap :: FinMap n a }

-- append and fromVector are duplicated exactly between the safe and unsafe
-- modules because they are used in comparative testing (and so implementations
-- must be available for both types).

-- | /O(min(n,W))/.
append :: NatRepr n -> a -> FinMap n a -> FinMap (n + 1) a
append k v sm =
  case NatRepr.leqSucc k of
    NatRepr.LeqProof -> insert (mkFin k) v (incMax sm)

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

-- | /O(min(n,W))/.
delete :: Fin n -> FinMap n a -> FinMap n a
delete k =
  FinMap . (IntMap.delete (fromIntegral (Fin.finToNat k))) . getFinMap

-- | Decrement the key/size, removing the item at key @n + 1@ if present.
decMax :: NatRepr n -> FinMap (n + 1) a -> FinMap n a
decMax k sm =
  let sm' = getFinMap sm
  in FinMap (IntMap.delete (fromIntegral (NatRepr.natValue k)) sm')
