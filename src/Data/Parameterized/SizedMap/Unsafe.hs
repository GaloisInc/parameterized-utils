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

module Data.Parameterized.SizedMap.Unsafe
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

-- | @'SizedMap' n a@ is a map with 'NatRepr' keys, @a@ values, and keys all
-- less than @n@ (and so, size up to @n@).
newtype SizedMap (n :: Nat) a = SizedMap { getSizedMap :: IntMap a }

instance Eq a => Eq (SizedMap n a) where
  sm1 == sm2 = getSizedMap sm1 == getSizedMap sm2

-- | Non-lawful instance, provided for testing
instance Show a => Show (SizedMap n a) where
  show sm = show (getSizedMap sm)

------------------------------------------------------------------------
-- Query

-- | /O(1)/. Is the map empty?
null :: SizedMap n a -> Bool
null = IntMap.null . getSizedMap
{-# INLINABLE null #-}

-- | /O(min(n,W))/. Get the value at the given key in the map.
lookup :: Fin n -> SizedMap n a -> Maybe a
lookup k = IntMap.lookup (fromIntegral (Fin.finToNat k)) . getSizedMap

-- This is pulled out as a function so that it's obvious that its use is safe
-- (since Natural is unbounded), whereas other uses of fromIntegral require more
-- careful reasoning.
intToNat :: Int -> Natural
intToNat = fromIntegral
{-# INLINE intToNat #-}

-- | /O(n)/. Number of elements in the map.
size :: forall n a. SizedMap n a -> Fin (n + 1)
size sm =
  case NatRepr.mkNatRepr (intToNat (IntMap.size (getSizedMap sm))) of
    Some (repr :: NatRepr m) ->
      case unsafeCoerce (NatRepr.LeqProof :: LeqProof 0 0) :: LeqProof (m + 1) (n + 1) of
        NatRepr.LeqProof -> mkFin @m @(n + 1) repr

------------------------------------------------------------------------
-- Construction

-- | /O(1)/. Increase maximum key/size.
--
-- Requires @n + 1 < (maxBound :: Int)@.
incMax :: SizedMap n a -> SizedMap (n + 1) a
incMax = SizedMap . getSizedMap
{-# INLINE incMax #-}

-- | /O(1)/. The empty map.
empty :: SizedMap 0 a
empty = SizedMap IntMap.empty
{-# INLINE empty #-}

-- | /O(1)/. A map with one element.
singleton :: a -> SizedMap 1 a
singleton = SizedMap . IntMap.singleton 0
{-# INLINABLE singleton #-}

-- | /O(min(n,W))/.
insert :: Fin n -> a -> SizedMap n a -> SizedMap n a
insert k v sm =
  SizedMap (IntMap.insert (fromIntegral (Fin.finToNat k)) v (getSizedMap sm))

newtype FlipMap a n = FlipMap { unFlipMap :: SizedMap n a }

-- append and fromVector are duplicated exactly between the safe and unsafe
-- modules because they are used in comparative testing (and so implementations
-- must be available for both types).

-- | /O(min(n,W))/.
append :: NatRepr n -> a -> SizedMap n a -> SizedMap (n + 1) a
append k v sm =
  case NatRepr.leqSucc k of
    NatRepr.LeqProof -> insert (mkFin k) v (incMax sm)

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

-- | /O(min(n,W))/.
delete :: Fin n -> SizedMap n a -> SizedMap n a
delete k =
  SizedMap . (IntMap.delete (fromIntegral (Fin.finToNat k))) . getSizedMap

-- | Decrement the key/size, removing the item at key @n + 1@ if present.
decMax :: NatRepr n -> SizedMap (n + 1) a -> SizedMap n a
decMax k sm =
  let sm' = getSizedMap sm
  in SizedMap (IntMap.delete (fromIntegral (NatRepr.natValue k)) sm')
