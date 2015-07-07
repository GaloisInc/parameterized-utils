------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Map
-- Description      : Indexed finite maps
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines finite maps where the key and value types are
-- parameterized by an arbitrary kind.
-- Some code was adapted from containers.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Parameterized.Map
  ( MapF
  , Data.Parameterized.Map.empty
  , lookup
  , insert
  , delete
  , union
  , map
  , elems
  , filterGt
  , filterLt
    -- * Complex interface.
  , UpdateRequest(..)
  , Updated(..)
  , updatedValue
  , updateAtKey
  , module Data.Parameterized.Classes
    -- * Internals
  , Pair
  ) where

import Control.Applicative
import Control.Monad.Identity
import Data.List (intercalate)
import Data.Maybe

import Data.Parameterized.Classes
import Data.Parameterized.Some
import Data.Parameterized.TraversableF
import Data.Parameterized.Utils.BinTree
  ( MaybeS(..)
  , fromMaybeS
  , Updated(..)
  , updatedValue
  , TreeApp(..)
  , bin
  , IsBinTreeM(..)
  , balanceL
  , balanceR
  , glue
  )
import qualified Data.Parameterized.Utils.BinTree as Bin

#if MIN_VERSION_base(4,8,0)
import Prelude hiding (lookup, map, traverse)
#else
import Prelude hiding (lookup, map)
#endif

------------------------------------------------------------------------
-- MapF

data MapF (ktp :: k -> *) (rtp :: k -> *) where
  Bin :: {-# UNPACK #-}
         !Size
      -> !(ktp a)
      -> !(rtp a)
      -> !(MapF ktp rtp)
      -> !(MapF ktp rtp)
      -> MapF ktp rtp
  Tip :: MapF ktp rtp

data Pair k a where
  Pair :: !(k tp) -> !(a tp) -> Pair k a

instance TestEquality k => Eq (Pair k a) where
  Pair x _ == Pair y _ = isJust (testEquality x y)

comparePair :: OrdF k => Pair k a -> Pair k a -> Ordering
comparePair (Pair x _) (Pair y _) = toOrdering (compareF x y)
{-# INLINABLE comparePair #-}


instance OrdF k => Ord (Pair k a) where
  compare = comparePair

type Size = Int

empty :: MapF ktp rtp
empty = Tip

singleton :: k tp -> a tp -> MapF k a
singleton k x = Bin 1 k x Tip Tip

instance Bin.IsBinTreeM (MapF k a) Identity (Pair k a) where
  asBin (Bin _ k v l r) = BinTree (Pair k v) l r
  asBin Tip = TipTree

  tip = Tip
  bin' (Pair k v) l r =
    Identity $! Bin (size l + size r + 1) k v l r

  size Tip              = 0
  size (Bin sz _ _ _ _) = sz

------------------------------------------------------------------------
-- Traversals

#ifdef __GLASGOW_HASKELL__
{-# NOINLINE [1] map #-}
{-# NOINLINE [1] traverse #-}
{-# RULES
"map/map" forall (f :: (forall tp . f tp -> g tp)) (g :: (forall tp . g tp -> h tp)) xs
               . map g (map f xs) = map (g . f) xs
"map/traverse" forall (f :: (forall tp . f tp -> m (g tp))) (g :: (forall tp . g tp -> h tp)) xs
               . fmap (map g) (traverse f xs) = traverse (\v -> g <$> f v) xs
"traverse/map"
  forall (f :: (forall tp . f tp -> g tp)) (g :: (forall tp . g tp -> m (h tp))) xs
       . traverse g (map f xs) = traverse (\v -> g (f v)) xs
"traverse/traverse"
  forall (f :: (forall tp . f tp -> m (g tp))) (g :: (forall tp . g tp -> m (h tp))) xs
       . traverse f xs >>= traverse g = traverse (\v -> f v >>= g) xs
 #-}
#endif

-- | Modify elements in a map
map :: (forall tp . f tp -> g tp) -> MapF ktp f -> MapF ktp g
map _ Tip = Tip
map f (Bin sx kx x l r) = Bin sx kx (f x) (map f l) (map f r)

-- | Traverse elements in a map
traverse :: Applicative m => (forall tp . f tp -> m (g tp)) -> MapF ktp f -> m (MapF ktp g)
traverse _ Tip = pure Tip
traverse f (Bin sx kx x l r) = Bin sx kx <$> f x <*> traverse f l <*> traverse f r

-- | Lookup value in map.
lookup :: OrdF k => k tp -> MapF k a -> Maybe (a tp)
lookup k0 = seq k0 (go k0)
  where
    go :: OrdF k => k tp -> MapF k a -> Maybe (a tp)
    go _ Tip = Nothing
    go k (Bin _ kx x l r) =
      case compareF k kx of
        LTF -> go k l
        GTF -> go k r
        EQF -> Just x
{-# INLINABLE lookup #-}

instance FunctorF (MapF ktp) where
  fmapF = map

instance FoldableF (MapF ktp) where
  foldrF f z = go z
    where go z' Tip             = z'
          go z' (Bin _ _ x l r) = go (f x (go z' r)) l

instance TraversableF (MapF ktp) where
  traverseF = traverse

instance (ShowF ktp, ShowF rtp) => Show (MapF ktp rtp) where
  show m = showMap showF showF m

-- | Return elements in the tree sorted by key.
elems :: MapF k a -> [Some a]
elems = foldrF (\e l -> Some e : l) []

-- | Perform a fold with the key also provided.
foldrWithKey :: (forall s . k s -> a s -> b -> b) -> b -> MapF k a -> b
foldrWithKey f z = go z
  where
    go z' Tip = z'
    go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l

showMap :: (forall tp . ktp tp -> String)
        -> (forall tp . rtp tp -> String)
        -> MapF ktp rtp
        -> String
showMap ppk ppv m = "{ " ++ intercalate ", " l ++ " }"
  where l = foldrWithKey (\k a l0 -> (ppk k ++ " -> " ++ ppv a) : l0) [] m

------------------------------------------------------------------------
-- filter

compareKeyPair :: OrdF k => k tp -> Pair k a -> Ordering
compareKeyPair k = \(Pair x _) -> toOrdering (compareF k x)

-- | @filterGt k m@ returns submap of @m@ that only contains entries
-- that are larger than @k@.
filterGt :: OrdF k => k tp -> MapF k v -> MapF k v
filterGt k m = fromMaybeS m (Bin.filterGt (compareKeyPair k) m)
{-# INLINABLE filterGt #-}

-- | @filterLt k m@ returns submap of @m@ that only contains entries
-- that are smaller than @k@.
filterLt :: OrdF k => k tp -> MapF k v -> MapF k v
filterLt k m = fromMaybeS m (Bin.filterLt (compareKeyPair k) m)
{-# INLINABLE filterLt #-}

------------------------------------------------------------------------
-- User operations

-- | Insert a binding into the map, replacing the existing
-- binding if needed.
insert :: OrdF k => k tp -> a tp -> MapF k a -> MapF k a
insert = \k v m -> seq k $ updatedValue (Bin.insert (Pair k v) m)
{-# INLINABLE insert #-}
{-# SPECIALIZE Bin.insert :: OrdF k => Pair k a -> MapF k a -> Updated (MapF k a) #-}


-- | Delete a value from the map if present.
delete :: OrdF k => k tp -> MapF k a -> MapF k a
delete = \k m -> seq k $ fromMaybeS m $ Bin.delete (p k) m
  where p :: OrdF k => k tp -> Pair k a -> Ordering
        p k (Pair kx _) = toOrdering (compareF k kx)
{-# INLINABLE delete #-}
{-# SPECIALIZE Bin.delete :: (Pair k a -> Ordering) -> MapF k a -> MaybeS (MapF k a) #-}

-- | Union two sets
union :: OrdF k => MapF k a -> MapF k a -> MapF k a
union t1 t2 = Bin.union t1 t2
{-# INLINABLE union #-}
{-# SPECIALIZE Bin.union :: OrdF k => MapF k a -> MapF k a -> MapF k a #-}

------------------------------------------------------------------------
-- updateAtKey

-- | Update request tells when to do with value
data UpdateRequest v
   = -- | Keep the current value.
     Keep
     -- | Set the value to a new value.
   | Set !v
     -- | Delete a value.
   | Delete

data AtKeyResult k a where
  AtKeyUnchanged :: AtKeyResult k a
  AtKeyInserted :: MapF k a -> AtKeyResult k a
  AtKeyModified :: MapF k a -> AtKeyResult k a
  AtKeyDeleted  :: MapF k a -> AtKeyResult k a

atKey' :: (OrdF k, Functor f)
       => k tp
       -> f (Maybe (a tp)) -- ^ Function to call if no element is found.
       -> (a tp -> f (UpdateRequest (a tp)))
       -> MapF k a
       -> f (AtKeyResult k a)
atKey' k onNotFound onFound t =
  case asBin t of
    TipTree -> ins <$> onNotFound
      where ins Nothing  = AtKeyUnchanged
            ins (Just v) = AtKeyInserted (singleton k v)
    BinTree yp@(Pair kx y) l r ->
      case compareF k kx of
        LTF -> ins <$> atKey' k onNotFound onFound l
          where ins AtKeyUnchanged = AtKeyUnchanged
                ins (AtKeyInserted l') = AtKeyInserted (balanceL yp l' r)
                ins (AtKeyModified l') = AtKeyModified (bin      yp l' r)
                ins (AtKeyDeleted  l') = AtKeyDeleted  (balanceR yp l' r)
        GTF -> ins <$> atKey' k onNotFound onFound r
          where ins AtKeyUnchanged = AtKeyUnchanged
                ins (AtKeyInserted r') = AtKeyInserted (balanceR yp l r')
                ins (AtKeyModified r') = AtKeyModified (bin      yp l r')
                ins (AtKeyDeleted  r') = AtKeyDeleted  (balanceL yp l r')
        EQF -> ins <$> onFound y
          where ins Keep    = AtKeyUnchanged
                ins (Set x) = AtKeyModified (bin (Pair kx x) l r)
                ins Delete  = AtKeyDeleted (glue l r)
{-# INLINABLE atKey' #-}

-- | Log-time algorithm that allows a value at a specific key to be added, replaced,
-- or deleted.
updateAtKey :: (OrdF k, Functor f)
            => k tp -- ^ Key to update
            -> f (Maybe (a tp))
               -- ^ Action to call if nothing is found
            -> (a tp -> f (UpdateRequest (a tp)))
               -- ^ Action to call if value is found.
            -> MapF k a
               -- ^ Map to update
            -> f (Updated (MapF k a))
updateAtKey k onNotFound onFound t = ins <$> atKey' k onNotFound onFound t
  where ins AtKeyUnchanged = Unchanged t
        ins (AtKeyInserted t') = Updated t'
        ins (AtKeyModified t') = Updated t'
        ins (AtKeyDeleted  t') = Updated t'
{-# INLINABLE updateAtKey #-}