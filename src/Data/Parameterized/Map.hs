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
--
-- This uses code taken from containers, but specialized to this case.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.Map
  ( MapF
  , empty
  , lookup
  , insert
  , delete
  , union

  , map
  , elems
    -- * Complex interface.
  , UpdateRequest(..)
  , Updated(..)
  , updatedValue
  , updateAtKey
  , module Data.Parameterized.Classes
  ) where

import Control.Applicative (Applicative(..), (<$>))
import Data.List (foldl', intercalate)
import Data.Maybe
import Prelude hiding (lookup, map)

import Data.Parameterized.Classes
import Data.Parameterized.Some
import Data.Parameterized.TraversableF

data MapF (ktp :: k -> *) (rtp :: k -> *) where
  Bin :: {-# UNPACK #-}
         !Size
      -> !(ktp a)
      -> !(rtp a)
      -> !(MapF ktp rtp)
      -> !(MapF ktp rtp)
      -> MapF ktp rtp
  Tip :: MapF ktp rtp

type Size = Int

empty :: MapF ktp rtp
empty = Tip

singleton :: k tp -> a tp -> MapF k a
singleton k x = Bin 1 k x Tip Tip

size :: MapF k a -> Int
size Tip              = 0
size (Bin sz _ _ _ _) = sz
{-# INLINE size #-}

------------------------------------------------------------------------
-- Traversals

-- | Modify elements in a
map :: (forall tp . f tp -> g tp) -> MapF ktp f -> MapF ktp g
map _ Tip = Tip
map f (Bin sx kx x l r) = Bin sx kx (f x) (map f l) (map f r)

#if __GLASGOW_HASKELL__ >= 709
{-# RULES
"map/coerce" map coerce = coerce
 #-}
#endif

-- | Modify elements in a
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
showMap ppk ppv m = "{ " ++ intercalate "," l ++ " }"
  where l = foldrWithKey (\k a l0 -> (ppk k ++ " -> " ++ ppv a) : l0) [] m

------------------------------------------------------------------------
-- Balancing operations

delta,ratio :: Int
delta = 3
ratio = 2

-- balanceL is called when left subtree might have been inserted to or when
-- right subtree might have been deleted from.
balanceL :: k tp -> a tp -> MapF k a -> MapF k a -> MapF k a
balanceL k x l r =
  case r of
    Tip ->
      case l of
        Tip -> Bin 1 k x Tip Tip
        (Bin _ _ _ Tip Tip) -> Bin 2 k x l Tip
        (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) -> Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
        (Bin _ lk lx ll@(Bin _ _ _ _ _) Tip) -> Bin 3 lk lx ll (Bin 1 k x Tip Tip)
        (Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr))
          | lrs < ratio*lls -> Bin (1+ls) lk lx ll (Bin (1+lrs) k x lr Tip)
          | otherwise -> Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+size lrr) k x lrr Tip)

    (Bin rs _ _ _ _) ->
      case l of
        Tip -> Bin (1+rs) k x Tip r

        (Bin ls lk lx ll lr)
          | ls > delta*rs ->
            case (ll, lr) of
              (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr)
                | lrs < ratio*lls -> Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                | otherwise -> Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+rs+size lrr) k x lrr r)
              (_, _) -> error "Failure in Data.Map.balanceL"
          | otherwise -> Bin (1+ls+rs) k x l r
{-# NOINLINE balanceL #-}

-- balanceR is called when right subtree might have been inserted to or when
-- left subtree might have been deleted from.
balanceR :: k tp -> a tp -> MapF k a -> MapF k a -> MapF k a
balanceR k x l r =
  case l of
    Tip ->
      case r of
        Tip -> Bin 1 k x Tip Tip
        (Bin _ _ _ Tip Tip) -> Bin 2 k x Tip r
        (Bin _ rk rx Tip rr@(Bin _ _ _ _ _)) -> Bin 3 rk rx (Bin 1 k x Tip Tip) rr
        (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) ->
          Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
        (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _))
          | rls < ratio*rrs -> Bin (1+rs) rk rx (Bin (1+rls) k x Tip rl) rr
          | otherwise ->
              Bin (1+rs)
                  rlk
                  rlx
                  (Bin (1+size rll) k x Tip rll)
                  (Bin (1+rrs+size rlr) rk rx rlr rr)

    (Bin ls _ _ _ _) ->
      case r of
        Tip -> Bin (1+ls) k x l Tip
        (Bin rs rk rx rl rr)
          | rs > delta*ls  ->
            case (rl, rr) of
              (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _)
                | rls < ratio*rrs -> Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                | otherwise -> Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
              (_, _) -> error "Failure in Data.Map.balanceR"
          | otherwise -> Bin (1+ls+rs) k x l r
{-# NOINLINE balanceR #-}

-- link is called to insert a key and value between two disjoint subtrees.
link :: k tp -> a tp -> MapF k a -> MapF k a -> MapF k a
link kx x Tip r  = insertMin kx x r
link kx x l Tip  = insertMax kx x l
link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL < sizeR  = balanceL kz z (link kx x l lz) rz
  | delta*sizeR < sizeL  = balanceR ky y ly (link kx x ry r)
  | otherwise            = Bin (sizeL + sizeR + 1) kx x l r

------------------------------------------------------------------------
-- MapCtx

-- | This represents the context of a tree outside a part of the tree
-- that may be modified.
data MapCtx k a where
  -- We did a computation that may modify the right subtree.
  ModRight :: !Size -> !(k tp) -> !(a tp) -> !(MapF k a) -> MapCtx k a
  -- We did a computation that may modify the left subtree.
  ModLeft  :: !Size -> !(k tp) -> !(a tp) -> !(MapF k a) -> MapCtx k a

-- | Update the tree after a value has been inserted into a subtree.
afterInsert :: [MapCtx k a] -> MapF k a -> MapF k a
afterInsert ctx m0 = foldl' go m0 ctx
  where go r (ModRight _ k v l) = balanceR k v l r
        go l (ModLeft  _ k v r) = balanceL k v l r

-- | Update the tree after a value has been modified.
afterModify :: [MapCtx k a] -> MapF k a -> MapF k a
afterModify ctx m0 = foldl' go m0 ctx
  where go r (ModRight sz k v l) = Bin sz k v l r
        go l (ModLeft  sz k v r) = Bin sz k v l r

-- | Update the tree after a value has been deleted.
afterDelete :: [MapCtx k a] -> MapF k a -> MapF k a
afterDelete ctx m0 = foldl' go m0 ctx
  where go r (ModRight _ k v l) = balanceL k v l r
        go l (ModLeft  _ k v r) = balanceR k v l r

------------------------------------------------------------------------
-- Modify minimal/maximal elements.

-- | Insert a new maximal element.
insertMax :: k tp -> a tp -> MapF k a -> MapF k a
insertMax kx x t =
  case t of
    Tip -> singleton kx x
    Bin _ ky y l r -> balanceR ky y l (insertMax kx x r)

-- | Insert a new minimal element.
insertMin :: k tp -> a tp -> MapF k a -> MapF k a
insertMin kx x t =
  case t of
    Tip -> singleton kx x
    Bin _ ky y l r -> balanceL ky y (insertMin kx x l) r

data SomePair k a where
  SomePair :: !(k tp) -> !(a tp) -> !(MapF k a) -> SomePair k a

-- | /O(log n)/. Delete and find the minimal element.
deleteFindMin :: MapF k a -> SomePair k a
deleteFindMin = go id
  where go f (Bin _ k x Tip r) = SomePair k x (f r)
        go f (Bin _ k x l   r) = go (\l' -> f (balanceR k x l' r)) l
        go _ Tip = error "Map.deleteFindMin: can not return the minimal element of an empty map"

-- | /O(log n)/. Delete and find the maximal element.
deleteFindMax :: MapF k a -> SomePair k a
deleteFindMax = go id
  where go f (Bin _ k x l Tip) = SomePair k x (f l)
        go f (Bin _ k x l r)   = go (\r' -> f (balanceL k x l r')) r
        go _ Tip = error "Map.deleteFindMax: can not return the maximal element of an empty map"

------------------------------------------------------------------------
-- filter

-- | @filterGt k m@ returns submap of @m@ that only contains entries
-- that are larger than @k@.
filterGt :: OrdF k => k tp -> MapF k v -> MapF k v
filterGt _   Tip = Tip
filterGt k (Bin _ kx x l r) =
  case compareF k kx of
    LTF -> link kx x (filterGt k l) r
    EQF -> r
    GTF -> filterGt k r

-- | @filterLt k m@ returns submap of @m@ that only contains entries
-- that are smaller than @k@.
filterLt :: OrdF k => k tp -> MapF k v -> MapF k v
filterLt _   Tip = Tip
filterLt k (Bin _ kx x l r) =
  case compareF kx k of
    LTF -> link kx x l (filterLt k r)
    EQF -> l
    GTF -> filterLt k l
{-# INLINABLE filterLt #-}

------------------------------------------------------------------------
-- User operations

-- See Note: Type of local 'go' function
insert :: OrdF k => k tp -> a tp -> MapF k a -> MapF k a
insert = \k -> seq k (go k)
  where
    go :: OrdF k => k tp -> a tp -> MapF k a -> MapF k a
    go kx x Tip = singleton kx x
    go kx x (Bin sz ky y l r) =
        case compareF kx ky of
            LTF -> balanceL ky y (go kx x l) r
            GTF -> balanceR ky y l (go kx x r)
            EQF -> Bin sz kx x l r
{-# INLINABLE insert #-}

-- glue l r glues two trees together.
-- Assumes that [l] and [r] are already balanced with respect to each other.
glue :: MapF k a -> MapF k a -> MapF k a
glue Tip r = r
glue l Tip = l
glue l r
  | size l > size r =
    case deleteFindMax l of
      SomePair km m l' -> balanceR km m l' r
  | otherwise =
    case deleteFindMin r of
      SomePair km m r' -> balanceL km m l r'

-- | Delete a value from the map if present.
delete :: OrdF k => k tp -> MapF k a -> MapF k a
delete = \k m -> seq k (go k m)
  where
    go :: OrdF k => k tp -> MapF k a -> MapF k a
    go _ Tip = Tip
    go k (Bin _ kx x l r) =
      case compareF k kx of
        LTF -> balanceR kx x (go k l) r
        GTF -> balanceL kx x l (go k r)
        EQF -> glue l r
{-# INLINABLE delete #-}

------------------------------------------------------------------------
-- updateAtKey

-- | Update request tells when to do with value
data UpdateRequest v where
  -- | Keep the current value.
  Keep :: UpdateRequest v
  -- | Set the value to a new value.
  Set :: !v -> UpdateRequest v
  -- | Delete a value.
  Delete :: UpdateRequest v

-- | Updated a contains a value that has been flagged on whether it was
-- modified by an operation.
data Updated a where
  Updated   :: !a -> Updated a
  Unchanged :: !a -> Updated a

updatedValue :: Updated a -> a
updatedValue (Updated a) = a
updatedValue (Unchanged a) = a

atKey' :: (OrdF k, Functor f)
       => MapF k a -- ^ Original map (returned if value is not changed).
       -> k tp
       -> f (Maybe (a tp)) -- ^ Function to call if no element is found.
       -> (a tp -> f (UpdateRequest (a tp)))
       -> [MapCtx k a]
       -> MapF k a
       -> f (Updated (MapF k a))
atKey' orig k onNotFound onFound ctx t =
  case t of
    Tip -> ins <$> onNotFound
      where ins Nothing  = Unchanged orig
            ins (Just v) = Updated (afterInsert ctx (singleton k v))
    Bin sz kx y l r ->
      case compareF k kx of
        LTF -> atKey' orig k onNotFound onFound ctx' l
          where ctx' = ModLeft sz kx y r : ctx
        GTF -> atKey' orig k onNotFound onFound ctx' r
          where ctx' = ModRight sz kx y l : ctx
        EQF -> ins <$> onFound y
          where ins Keep = Unchanged orig
                ins (Set x) = Updated (afterModify ctx (Bin sz kx x l r))
                ins Delete  = Updated (afterDelete ctx (glue l r))

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
updateAtKey k onNotFound onFound t = atKey' t k onNotFound onFound [] t

------------------------------------------------------------------------
-- Union

-- Insert a new key and value in the map if it is not already present.
-- Used by `union`.
insertR :: OrdF k => k tp -> a tp -> MapF k a -> MapF k a
insertR  = \k v m -> seq k (go m k v m id)
  where
    go :: OrdF k => r -> k tp -> a tp -> MapF k a -> (MapF k a -> r) -> r
    go _ kx x Tip f = f (singleton kx x)
    go orig kx x (Bin _ ky y l r) f =
        case compareF kx ky of
          LTF -> go orig kx x l (\l' -> f (balanceL ky y l' r))
          GTF -> go orig kx x r (\r' -> f (balanceR ky y l r'))
          EQF -> orig

-- | Union two sets
union :: OrdF k => MapF k a -> MapF k a -> MapF k a
union Tip t2  = t2
union t1 Tip  = t1
union t1  (Bin _ kx x Tip Tip) = insertR kx x t1
union (Bin _ kx x l r) t2 = link kx x (hedgeUnion_UB    kx l t2)
                                      (hedgeUnion_LB kx    r t2)
{-# INLINABLE union #-}

-- | Hedge union where we only add elements in second map if key is
-- strictly above a lower bound.
hedgeUnion_LB :: OrdF k => k tp -> MapF k b -> MapF k b -> MapF k b
hedgeUnion_LB lo t1 t2 =
  case (t1, t2) of
    (_, Tip) -> t1
    (Tip, _) -> filterGt lo t2
    -- Prune left tree.
    (_, Bin _ k _ _ r) | k `leqF` lo -> hedgeUnion_LB lo t1 r
    -- Special case when t2 is a single element.
    (_,   Bin _ kx x Tip Tip) -> insertR kx x t1
    -- Split on left-and-right subtrees of t1.
    (Bin _ kx x l r, _) -> link kx x (hedgeUnion_LB_UB lo kx l t2)
                                     (hedgeUnion_LB    kx    r t2)
{-# INLINABLE hedgeUnion_LB #-}

-- | Hedge union where we only add elements in second map if key is
-- strictly below a upper bound.
hedgeUnion_UB :: OrdF k => k tp -> MapF k b -> MapF k b -> MapF k b
hedgeUnion_UB hi t1 t2 =
  case (t1, t2) of
    (_, Tip) -> t1
    (Tip, _) -> filterLt hi t2
    -- Prune right tree.
    (_, Bin _ kx _ l _) | kx `geqF` hi -> hedgeUnion_UB hi t1 l
    -- Special case when t2 is a single element.
    (_, Bin _ kx x Tip Tip)  -> insertR kx x t1
    -- Split on left-and-right subtrees of t1.
    (Bin _ kx x l r, _) -> link kx x (hedgeUnion_UB       kx l t2)
                                     (hedgeUnion_LB_UB kx hi r t2)
{-# INLINABLE hedgeUnion_UB #-}

-- | Hedge union where we only add elements in second map if key is
-- strictly between a lower and upper bound.
hedgeUnion_LB_UB :: OrdF k => k u -> k v -> MapF k b -> MapF k b -> MapF k b
hedgeUnion_LB_UB lo hi t1 t2 =
  case (t1, t2) of
    (_, Tip) -> t1
    -- Prune left tree.
    (_,   Bin _ k _ _ r) | k `leqF` lo -> hedgeUnion_LB_UB lo hi t1 r
    -- Prune right tree.
    (_,   Bin _ k _ l _) | k `geqF` hi -> hedgeUnion_LB_UB lo hi t1 l
    -- When t1 becomes empty (assumes lo <= k <= hi)
    (Tip, Bin _ kx x l r) -> link kx x (filterGt lo l) (filterLt hi r)
    -- Special when t2 is a single element.
    (_,   Bin _ kx x Tip Tip) -> insertR kx x t1
    -- Split on left-and-right subtrees of t1.
    (Bin _ kx x l r, _) ->
      link kx x (hedgeUnion_LB_UB lo kx l t2)
                (hedgeUnion_LB_UB kx hi r t2)
{-# INLINABLE hedgeUnion_LB_UB #-}