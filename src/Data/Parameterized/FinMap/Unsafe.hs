{-|
Copyright        : (c) Galois, Inc 2022

See "Data.Parameterized.FinMap".
-}

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
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

import           Data.Functor.WithIndex (FunctorWithIndex(imap))
import           Data.Foldable.WithIndex (FoldableWithIndex(ifoldMap))
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import           GHC.TypeLits (KnownNat, Nat)
import           Numeric.Natural (Natural)
import           Unsafe.Coerce (unsafeCoerce)

import           Data.Parameterized.Fin (Fin, mkFin)
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.NatRepr (LeqProof, NatRepr, type (+), type (<=))
import qualified Data.Parameterized.NatRepr as NatRepr
import           Data.Parameterized.Some (Some(Some))
import           Data.Parameterized.Vector (Vector)
import qualified Data.Parameterized.Vector as Vec

-- This is pulled out as a function so that it's obvious that its use is safe
-- (since Natural is unbounded).
intToNat :: Int -> Natural
intToNat = fromIntegral
{-# INLINE intToNat #-}

-- These are pulled out as functions so that it's obvious that their use is
-- unsafe (since Natural is unbounded).

unsafeFinToInt :: Fin n -> Int
unsafeFinToInt = fromIntegral . Fin.finToNat
{-# INLINE unsafeFinToInt #-}

unsafeNatReprToInt :: NatRepr n -> Int
unsafeNatReprToInt = fromIntegral . NatRepr.natValue
{-# INLINE unsafeNatReprToInt #-}

------------------------------------------------------------------------
-- Type

-- This datatype has two important invariants:
--
-- * Its keys must be less than the nat in its type.
-- * Its size must be less than the maximum Int.
--
-- If these invariants hold, all of the unsafe operations in this module
-- (fromJust, unsafeCoerce) will work as intended.

-- | @'FinMap' n a@ is a map with @'Fin' n@ keys and @a@ values.
newtype FinMap (n :: Nat) a = FinMap { getFinMap :: IntMap a }

instance Eq a => Eq (FinMap n a) where
  fm1 == fm2 = getFinMap fm1 == getFinMap fm2
  {-# INLINABLE (==) #-}

instance Functor (FinMap n) where
  fmap f = FinMap . fmap f . getFinMap
  {-# INLINABLE fmap #-}

instance Foldable (FinMap n) where
  foldMap f = foldMap f . getFinMap
  {-# INLINABLE foldMap #-}

instance FunctorWithIndex (Fin n) (FinMap n) where
  imap f = FinMap . IntMap.mapWithKey (f . unsafeFin) . getFinMap
  -- Inline so that RULES for IntMap.mapWithKey can fire
  {-# INLINE imap #-}

instance FoldableWithIndex (Fin n) (FinMap n) where
  ifoldMap f = IntMap.foldMapWithKey (f . unsafeFin) . getFinMap

-- | Non-lawful instance, provided for testing
instance Show a => Show (FinMap n a) where
  show fm = show (getFinMap fm)
  {-# INLINABLE show #-}

------------------------------------------------------------------------
-- Query

-- | /O(1)/. Is the map empty?
null :: FinMap n a -> Bool
null = IntMap.null . getFinMap
{-# INLINABLE null #-}

-- | /O(min(n,W))/. Fetch the value at the given key in the map.
lookup :: Fin n -> FinMap n a -> Maybe a
lookup k = IntMap.lookup (unsafeFinToInt k) . getFinMap
{-# INLINABLE lookup #-}

-- | Unsafely create a @'Fin' n@ from an 'Int' which is known to be less than
-- @n@ for reasons not visible to the type system.
unsafeFin :: forall n. Int -> Fin n
unsafeFin i =
  case NatRepr.mkNatRepr (intToNat i) of
    Some (repr :: NatRepr m) ->
      case unsafeCoerce (NatRepr.LeqProof :: LeqProof 0 0) :: LeqProof (m + 1) n of
        NatRepr.LeqProof -> mkFin @m @n repr

-- | /O(1)/. Number of elements in the map.
size :: forall n a. FinMap n a -> Fin (n + 1)
size = unsafeFin . IntMap.size . getFinMap
{-# INLINEABLE size #-}

------------------------------------------------------------------------
-- Construction

-- | /O(1)/. Increase maximum key/size by 1.
--
-- This does not alter the key-value pairs in the map, but rather increases the
-- maximum number of key-value pairs that the map can hold. See
-- "Data.Parameterized.FinMap" for more information.
--
-- Requires @n + 1 < (maxBound :: Int)@.
incMax :: FinMap n a -> FinMap (n + 1) a
incMax = FinMap . getFinMap
{-# INLINE incMax #-}

-- | /O(1)/. Increase maximum key/size.
--
-- Requires @m < (maxBound :: Int)@.
embed :: (n <= m) => NatRepr m -> FinMap n a -> FinMap m a
embed _ = FinMap . getFinMap
{-# INLINE embed #-}

-- | /O(1)/. The empty map.
empty :: KnownNat n => FinMap n a
empty = FinMap IntMap.empty
{-# INLINE empty #-}

-- | /O(1)/. A map with one element.
singleton :: a -> FinMap 1 a
singleton = FinMap . IntMap.singleton 0
{-# INLINABLE singleton #-}

-- | /O(min(n,W))/.
insert :: Fin n -> a -> FinMap n a -> FinMap n a
insert k v = FinMap . IntMap.insert (unsafeFinToInt k) v . getFinMap
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
    NatRepr.LeqProof -> insert (mkFin k) v (incMax fm)

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

-- | /O(min(n,W))/.
delete :: Fin n -> FinMap n a -> FinMap n a
delete k = FinMap . IntMap.delete (unsafeFinToInt k) . getFinMap
{-# INLINABLE delete #-}

-- | Decrement the key/size, removing the item at key @n + 1@ if present.
decMax :: NatRepr n -> FinMap (n + 1) a -> FinMap n a
decMax k = FinMap . IntMap.delete (unsafeNatReprToInt k) . getFinMap
{-# INLINABLE decMax #-}

mapWithKey :: (Fin n -> a -> b) -> FinMap n a -> FinMap n b
mapWithKey f = FinMap . IntMap.mapWithKey (f . unsafeFin) . getFinMap
-- Inline so that RULES for IntMap.mapWithKey can fire
{-# INLINE mapWithKey #-}
