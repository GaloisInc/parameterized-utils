------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Map
-- Copyright        : (c) Galois, Inc 2014-2015
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
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE Trustworthy #-}
module Data.Parameterized.Map
  ( MapF
  , Data.Parameterized.Map.empty
  , null
  , singleton
  , lookup
  , insert
  , insertWith
  , delete
  , union
  , map
  , elems
  , filterGt
  , filterLt
  , fromList
  , foldrWithKey
  , toList
  , size
  , traverseWithKey
    -- * Complex interface.
  , UpdateRequest(..)
  , Updated(..)
  , updatedValue
  , updateAtKey
  , mergeWithKeyM
  , module Data.Parameterized.Classes
    -- * Pair
  , Pair(..)
  ) where

import Control.Applicative
import Control.Monad.Identity
import Data.List (intercalate, foldl')
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
  , IsBinTree(..)
  , balanceL
  , balanceR
  , glue
  )
import qualified Data.Parameterized.Utils.BinTree as Bin

#if MIN_VERSION_base(4,8,0)
import Prelude hiding (lookup, map, traverse, null)
#else
import Prelude hiding (lookup, map, null)
#endif

------------------------------------------------------------------------
-- Pair

data Pair k a where
  Pair :: !(k tp) -> !(a tp) -> Pair k a

instance TestEquality k => Eq (Pair k a) where
  Pair x _ == Pair y _ = isJust (testEquality x y)

comparePair :: OrdF k => Pair k a -> Pair k a -> Ordering
comparePair (Pair x _) (Pair y _) = toOrdering (compareF x y)
{-# INLINABLE comparePair #-}

instance OrdF k => Ord (Pair k a) where
  compare = comparePair

------------------------------------------------------------------------
-- MapF

data MapF (k :: v -> *) (a :: v -> *) where
  Bin :: {-# UNPACK #-}
         !Size
      -> !(k x)
      -> !(a x)
      -> !(MapF k a)
      -> !(MapF k a)
      -> MapF k a
  Tip :: MapF k a

type Size = Int

-- | Return empty map
empty :: MapF k a
empty = Tip

-- | Return true if map is empty
null :: MapF k a -> Bool
null Tip = True
null Bin{} = False

-- | Return map containing a single element
singleton :: k tp -> a tp -> MapF k a
singleton k x = Bin 1 k x Tip Tip

instance Bin.IsBinTree (MapF k a) (Pair k a) where
  asBin (Bin _ k v l r) = BinTree (Pair k v) l r
  asBin Tip = TipTree

  tip = Tip
  bin (Pair k v) l r = Bin (size l + size r + 1) k v l r

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

-- | Traverse elements in a map
traverseWithKey
  :: Applicative m
  => (forall tp . ktp tp -> f tp -> m (g tp))
  -> MapF ktp f
  -> m (MapF ktp g)
traverseWithKey _ Tip = pure Tip
traverseWithKey f (Bin sx kx x l r) =
   Bin sx kx <$> f kx x <*> traverseWithKey f l <*> traverseWithKey f r

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

-- | Insert a binding into the map, replacing the existing binding if needed.
insert :: OrdF k => k tp -> a tp -> MapF k a -> MapF k a
insert = \k v m -> seq k $ updatedValue (Bin.insert (Pair k v) m)
{-# INLINABLE insert #-}
{-# SPECIALIZE Bin.insert :: OrdF k => Pair k a -> MapF k a -> Updated (MapF k a) #-}

-- | Insert a binding into the map, replacing the existing binding if needed.
insertWithImpl :: OrdF k => (a tp -> a tp -> a tp) -> k tp -> a tp -> MapF k a -> Updated (MapF k a)
insertWithImpl f k v t = seq k $
  case t of
    Tip -> Bin.Updated (Bin 1 k v Tip Tip)
    Bin sz yk yv l r ->
      case compareF k yk of
        LTF ->
          case insertWithImpl f k v l of
            Bin.Updated l'   -> Bin.Updated   (Bin.balanceL (Pair yk yv) l' r)
            Bin.Unchanged l' -> Bin.Unchanged (Bin sz yk yv l' r)
        GTF ->
          case insertWithImpl f k v r of
            Bin.Updated r'   -> Bin.Updated   (Bin.balanceR (Pair yk yv) l r')
            Bin.Unchanged r' -> Bin.Unchanged (Bin sz yk yv l r')
        EQF -> Bin.Unchanged (Bin sz yk (f v yv) l r)
{-# INLINABLE insertWithImpl #-}

-- | @insertWith f new m@ inserts the binding into @m@.
--
-- It inserts @f new old@ if @m@ already contains an equivaltn value
-- @old@, and @new@ otherwise.  It returns an Unchanged value if the
-- map stays the same size and an updated value if a new entry was
-- inserted.
insertWith :: OrdF k => (a tp -> a tp -> a tp) -> k tp -> a tp -> MapF k a -> MapF k a
insertWith = \f k v t -> seq k $ updatedValue (insertWithImpl f k v t)
{-# INLINABLE insertWith #-}

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

-- | Create a Map from a list of pairs.
fromList :: OrdF k => [Pair k a] -> MapF k a
fromList = foldl' (\m (Pair k a) -> insert k a m) Data.Parameterized.Map.empty

toList :: MapF k a -> [Pair k a]
toList = foldrWithKey (\k x m -> Pair k x : m) []

filterGtMaybe :: OrdF k => MaybeS (k x) -> MapF k a -> MapF k a
filterGtMaybe NothingS m = m
filterGtMaybe (JustS k) m = filterGt k m

filterLtMaybe :: OrdF k => MaybeS (k x) -> MapF k a -> MapF k a
filterLtMaybe NothingS m = m
filterLtMaybe (JustS k) m = filterLt k m

mergeWithKeyM :: forall k a b c m
               . (Applicative m, OrdF k)
              => (forall tp . k tp -> a tp -> b tp -> m (Maybe (c tp)))
              -> (MapF k a -> m (MapF k c))
              -> (MapF k b -> m (MapF k c))
              -> MapF k a
              -> MapF k b
              -> m (MapF k c)
mergeWithKeyM f g1 g2 = go
  where
    go Tip t2 = g2 t2
    go t1 Tip = g1 t1
    go t1 t2 = hedgeMerge NothingS NothingS t1 t2

    hedgeMerge :: MaybeS (k x) -> MaybeS (k y) -> MapF k a -> MapF k b -> m (MapF k c)
    hedgeMerge _   _   t1  Tip = g1 t1
    hedgeMerge blo bhi Tip (Bin _ kx x l r) =
      g2 $ Bin.link (Pair kx x) (filterGtMaybe blo l) (filterLtMaybe bhi r)
    hedgeMerge blo bhi (Bin _ kx x l r) t2 =
        let Bin.PairS found trim_t2 = trimLookupLo kx bhi t2
            resolve_g1 :: MapF k c -> MapF k c -> MapF k c -> MapF k c
            resolve_g1 Tip = Bin.merge
            resolve_g1 (Bin _ k' x' Tip Tip) = Bin.link (Pair k' x')
            resolve_g1 _ = error "mergeWithKey: Bad function g1"
            resolve_f Nothing = Bin.merge
            resolve_f (Just x') = Bin.link (Pair kx x')
         in case found of
              Nothing ->
                resolve_g1 <$> g1 (singleton kx x)
                           <*> hedgeMerge blo bmi l (trim blo bmi t2)
                           <*> hedgeMerge bmi bhi r trim_t2
              Just x2 ->
                resolve_f <$> f kx x x2
                          <*> hedgeMerge blo bmi l (trim blo bmi t2)
                          <*> hedgeMerge bmi bhi r trim_t2
      where bmi = JustS kx
{-# INLINE mergeWithKeyM #-}

{--------------------------------------------------------------------
  [trim blo bhi t] trims away all subtrees that surely contain no
  values between the range [blo] to [bhi]. The returned tree is either
  empty or the key of the root is between @blo@ and @bhi@.
--------------------------------------------------------------------}
trim :: OrdF k => MaybeS (k x) -> MaybeS (k y) -> MapF k a -> MapF k a
trim NothingS   NothingS   t = t
trim (JustS lk) NothingS   t = filterGt lk t
trim NothingS   (JustS hk) t = filterLt hk t
trim (JustS lk) (JustS hk) t = filterMiddle lk hk t

-- | Returns only entries that are strictly between the two keys.
filterMiddle :: OrdF k => k x -> k y -> MapF k a -> MapF k a
filterMiddle lo hi (Bin _ k _ _ r)
  | k `leqF` lo = filterMiddle lo hi r
filterMiddle lo hi (Bin _ k _ l _)
  | k `geqF` hi = filterMiddle lo hi l
filterMiddle _  _  t = t
{-# INLINABLE filterMiddle #-}



-- Helper function for 'mergeWithKey'. The @'trimLookupLo' lk hk t@ performs both
-- @'trim' (JustS lk) hk t@ and @'lookup' lk t@.

-- See Note: Type of local 'go' function
trimLookupLo :: OrdF k => k tp -> MaybeS (k y) -> MapF k a -> Bin.PairS (Maybe (a tp)) (MapF k a)
trimLookupLo lk NothingS t = greater lk t
  where greater :: OrdF k => k tp -> MapF k a -> Bin.PairS (Maybe (a tp)) (MapF k a)
        greater lo t'@(Bin _ kx x l r) =
           case compareF lo kx of
             LTF -> Bin.PairS (lookup lo l) t'
             EQF -> Bin.PairS (Just x) r
             GTF -> greater lo r
        greater _ Tip = Bin.PairS Nothing Tip
trimLookupLo lk (JustS hk) t = middle lk hk t
  where middle :: OrdF k => k tp -> k y -> MapF k a -> Bin.PairS (Maybe (a tp)) (MapF k a)
        middle lo hi t'@(Bin _ kx x l r) =
          case compareF lo kx of
            LTF | kx `ltF` hi -> Bin.PairS (lookup lo l) t'
                | otherwise -> middle lo hi l
            EQF -> Bin.PairS (Just x) (lesser hi r)
            GTF -> middle lo hi r
        middle _ _ Tip = Bin.PairS Nothing Tip

        lesser :: OrdF k => k y -> MapF k a -> MapF k a
        lesser hi (Bin _ k _ l _) | k `geqF` hi = lesser hi l
        lesser _ t' = t'
