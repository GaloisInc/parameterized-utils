------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.BinTree
-- Description      : Provides utilities for working with balanced binary trees.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines utilities for working with balanced binary trees.
------------------------------------------------------------------------
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Parameterized.Utils.BinTree
  ( MaybeS(..)
  , fromMaybeS
  , Updated(..)
  , updatedValue
  , TreeApp(..)
  , IsBinTree
  , bin
  , IsBinTreeM(..)
  , balanceL
  , balanceR
  , glue
  , filterGt
  , filterLt
  , insert
  , delete
  , union
  ) where

import Control.Applicative
import Control.Monad.Identity

------------------------------------------------------------------------
-- MaybeS

data MaybeS v
   = JustS !v
   | NothingS

instance Functor MaybeS where
  fmap _ NothingS = NothingS
  fmap f (JustS v) = JustS (f v)

instance Alternative MaybeS where
  empty = NothingS
  mv@JustS{} <|> _ = mv
  NothingS <|> v = v

instance Applicative MaybeS where
  pure = JustS

  NothingS <*> _ = NothingS
  JustS{} <*> NothingS = NothingS
  JustS f <*> JustS x = JustS (f x)

fromMaybeS :: a -> MaybeS a -> a
fromMaybeS r NothingS = r
fromMaybeS _ (JustS v) = v

------------------------------------------------------------------------
-- Updated

-- | Updated a contains a value that has been flagged on whether it was
-- modified by an operation.
data Updated a
   = Updated   !a
   | Unchanged !a

updatedValue :: Updated a -> a
updatedValue (Updated a) = a
updatedValue (Unchanged a) = a

------------------------------------------------------------------------
-- IsBinTree

data TreeApp p t
   = BinTree !p !t !t
   | TipTree

class (Applicative m, Monad m) => IsBinTreeM c m e | c -> e, c -> m where
  asBin :: c -> TreeApp e c
  tip :: c

  bin' :: e -> c -> c -> m c
  size :: c -> Int

binM :: IsBinTreeM c m e => e -> m c -> m c -> m c
binM c mx my = do
  x <- mx
  y <- my
  bin' c x y

class IsBinTreeM c Identity e => IsBinTree c e where
 bin :: e -> c -> c -> c
 bin p l r = runIdentity (bin' p l r)

-- bin :: IsBinTree c e => e -> c -> c -> c
-- bin = \x l r -> runIdentity (bin' x l r)
-- {-# INLINE bin #-}

delta,ratio :: Int
delta = 3
ratio = 2

-- balanceL is called when left subtree might have been inserted to or when
-- right subtree might have been deleted from.
balanceLM :: IsBinTreeM c m e => e -> c -> c -> m c
balanceLM p l r = do
  case asBin l of
    BinTree l_pair ll lr | size l > max 1 (delta*size r) ->
      case asBin lr of
        BinTree lr_pair lrl lrr | size lr >= max 2 (ratio*size ll) ->
          binM lr_pair (binM l_pair (pure ll) (pure lrl)) (binM p (pure lrr) (pure r))
        _ -> binM l_pair (pure ll) (binM p (pure lr) (pure r))

    _ -> binM p (pure l) (pure r)
{-# INLINE balanceLM #-}
{-# SPECIALIZE balanceLM :: IsBinTree c e => e -> c -> c -> Identity c #-}

-- balanceR is called when right subtree might have been inserted to or when
-- left subtree might have been deleted from.
balanceRM :: IsBinTreeM c m e => e -> c -> c -> m c
balanceRM p l r = do
  case asBin r of
    BinTree r_pair rl rr | size r > max 1 (delta*size l) ->
      case asBin rl of
        BinTree rl_pair rll rlr | size rl >= max 2 (ratio*size rr) ->
          (binM rl_pair $! bin' p l rll) $! bin' r_pair rlr rr
        _ -> do
          l_p_rl <- bin' p l rl
          bin' r_pair l_p_rl rr

    _ -> bin' p l r
{-# INLINE balanceRM #-}
{-# SPECIALIZE balanceRM :: IsBinTree c e => e -> c -> c -> Identity c #-}

-- balanceL is called when left subtree might have been inserted to or when
-- right subtree might have been deleted from.
balanceL :: IsBinTree c e => e -> c -> c -> c
balanceL p l r = runIdentity (balanceLM p l r)
{-
balanceL p l r = do
  case asBin l of
    BinTree l_pair ll lr | size l > max 1 (delta*size r) ->
      case asBin lr of
        BinTree lr_pair lrl lrr | size lr >= max 2 (ratio*size ll) ->
          bin lr_pair (bin l_pair ll lrl) (bin p lrr r)
        _ -> bin l_pair ll (bin p lr r)
    _ -> bin p l r
-}
{-# INLINE balanceL #-}


-- balanceR is called when right subtree might have been inserted to or when
-- left subtree might have been deleted from.
balanceR :: IsBinTree c e => e -> c -> c -> c
balanceR p l r = runIdentity (balanceRM p l r)
{-
balanceR p l r = do
  case asBin r of
    BinTree r_pair rl rr | size r > max 1 (delta*size l) ->
      case asBin rl of
        BinTree rl_pair rll rlr | size rl >= max 2 (ratio*size rr) ->
          bin rl_pair (bin p l rll) (bin r_pair rlr rr)
        _ -> bin r_pair (bin p l rl) rr

    _ -> bin p l r
-}
{-# INLINE balanceR #-}

-- | Insert a new maximal element.
insertMax :: IsBinTree c e => e -> c -> c
insertMax p t =
  case asBin t of
    TipTree -> bin p tip tip
    BinTree q l r -> balanceR q l (insertMax p r)

-- | Insert a new minimal element.
insertMin :: IsBinTree c e => e -> c -> c
insertMin p t =
  case asBin t of
    TipTree -> bin p tip tip
    BinTree q l r -> balanceL q (insertMin p l) r

-- link is called to insert a key and value between two disjoint subtrees.
link :: IsBinTree c e => e -> c -> c -> c
link p l r =
  case (asBin l, asBin r) of
    (TipTree, _) -> insertMin p r
    (_, TipTree) -> insertMax p l
    (BinTree py ly ry, BinTree pz lz rz)
     | delta*size l < size r -> balanceL pz (link p l lz) rz
     | delta*size r < size l -> balanceR py ly (link p ry r)
     | otherwise             -> bin p l r
{-# INLINE link #-}

data PairS f s = PairS !f !s

deleteFindMin :: IsBinTree c e => e -> c -> c -> PairS e c
deleteFindMin p l r =
  case asBin l of
    TipTree -> PairS p r
    BinTree lp ll lr ->
      case deleteFindMin lp ll lr of
        PairS q l' -> PairS q (balanceR p l' r)
{-# INLINABLE deleteFindMin #-}

deleteFindMax :: IsBinTree c e => e -> c -> c -> PairS e c
deleteFindMax p l r =
  case asBin r of
    TipTree -> PairS p l
    BinTree rp rl rr ->
      case deleteFindMax rp rl rr of
        PairS q r' -> PairS q (balanceL p l r')
{-# INLINABLE deleteFindMax #-}

-- glue l r glues two trees together.
-- Assumes that [l] and [r] are already balanced with respect to each other.
glue :: IsBinTree c e => c -> c -> c
glue l r =
  case (asBin l, asBin r) of
    (TipTree, _) -> r
    (_, TipTree) -> l
    (BinTree lp ll lr, BinTree rp rl rr)
     | size l > size r ->
       case deleteFindMax lp ll lr of
         PairS q l' -> balanceR q l' r
     | otherwise ->
       case deleteFindMin rp rl rr of
         PairS q r' -> balanceL q l r'
{-# INLINABLE glue #-}

------------------------------------------------------------------------
-- Ordered operations

-- | @insert' p m@ inserts the binding into @m@.  It returns
-- an Unchanged value if the map stays the same size and an updated
-- value if a new entry was inserted.
insert :: (IsBinTree c e, Ord e) => e -> c -> Updated c
--insert x t = runIdentity (insertM x t)
insert x t =
  case asBin t of
    TipTree -> Updated (bin x tip tip)
    BinTree y l r ->
      case compare x y of
        LT ->
          case insert x l of
            Updated l'   -> Updated   (balanceL y l' r)
            Unchanged l' -> Unchanged (bin       y l' r)
        GT ->
          case insert x r of
            Updated r'   -> Updated   (balanceR y l r')
            Unchanged r' -> Unchanged (bin       y l r')
        EQ -> Unchanged (bin x l r)
{-# INLINABLE insert #-}

insertM :: (IsBinTreeM c m e, Ord e) => e -> c -> m (Updated c)
insertM x t =
  case asBin t of
    TipTree -> Updated <$> bin' x tip tip
    BinTree y l r ->
      case compare x y of
        LT -> do
          ml <- insertM x l
          case ml of
            Updated l'   -> Updated   <$> balanceLM y l' r
            Unchanged l' -> Unchanged <$> bin'      y l' r
        GT -> do
          mr <- insertM x r
          case mr of
            Updated r'   -> Updated   <$> balanceRM y l r'
            Unchanged r' -> Unchanged <$> bin'      y l r'
        EQ -> Unchanged <$> bin' x l r
{-# INLINABLE insertM #-}
{-# SPECIALIZE insertM :: (IsBinTree c e, Ord e) => e -> c -> Identity (Updated c) #-}

delete :: IsBinTree c e
       => (e -> Ordering)
          -- ^ Predicate that returns whether the entry is less than, greater than, or equal
          -- to the key we are entry that we are looking for.
       -> c
       -> MaybeS c
delete k t =
  case asBin t of
    TipTree -> NothingS
    BinTree p l r ->
      case k p of
        LT -> (\l' -> balanceR p l' r) <$> delete k l
        GT -> (\r' -> balanceL p l r') <$> delete k r
        EQ -> JustS (glue l r)
{-# INLINABLE delete #-}

------------------------------------------------------------------------
-- filter

filterGt :: IsBinTree c e => (e -> Ordering) -> c -> MaybeS c
filterGt k t =
  case asBin t of
    TipTree -> NothingS
    BinTree x l r ->
      case k x of
        LT -> (\l' -> link x l' r) <$> filterGt k l
        GT -> filterGt k r <|> JustS r
        EQ -> JustS r
{-# INLINABLE filterGt #-}


-- | @filterLt' k m@ returns submap of @m@ that only contains entries
-- that are smaller than @k@.  If no entries are deleted then return Nothing.
filterLt :: IsBinTree c e => (e -> Ordering) -> c -> MaybeS c
filterLt k t =
  case asBin t of
    TipTree -> NothingS
    BinTree x l r ->
      case k x of
        LT -> filterLt k l <|> JustS l
        GT -> (\r' -> link x l r') <$> filterLt k r
        EQ -> JustS l
{-# INLINABLE filterLt #-}

------------------------------------------------------------------------
-- Union

-- Insert a new key and value in the map if it is not already present.
-- Used by `union`.
insertR :: (IsBinTree c e, Ord e) => e -> c -> c
insertR e m = fromMaybeS m (go e m)
  where
    go :: (IsBinTree c e, Ord e) => e -> c -> MaybeS c
    go x t =
      case asBin t of
        TipTree -> JustS (bin x tip tip)
        BinTree y l r ->
          case compare x y of
            LT -> (\l' -> balanceL y l' r) <$> go x l
            GT -> (\r' -> balanceR y l r') <$> go x r
            EQ -> NothingS
{-# INLINABLE insertR #-}

-- | Union two sets
union :: (IsBinTree c e, Ord e) => c -> c -> c
union t1 t2 =
  case (asBin t1, asBin t2) of
    (TipTree, _) -> t2
    (_, TipTree) -> t1
    (_, BinTree p (asBin -> TipTree) (asBin -> TipTree)) -> insertR p t1
    (BinTree x l r, _) ->
      link x
           (hedgeUnion_UB   x l t2)
           (hedgeUnion_LB x   r t2)
{-# INLINABLE union #-}

-- | Hedge union where we only add elements in second map if key is
-- strictly above a lower bound.
hedgeUnion_LB :: (IsBinTree c e, Ord e) => e -> c -> c -> c
hedgeUnion_LB lo t1 t2 =
  case (asBin t1, asBin t2) of
    (_, TipTree) -> t1
    (TipTree, _) -> fromMaybeS t2 (filterGt (compare lo) t2)
    -- Prune left tree.
    (_, BinTree k _ r) | k <= lo -> hedgeUnion_LB lo t1 r
    -- Special case when t2 is a single element.
    (_, BinTree x (asBin -> TipTree) (asBin -> TipTree)) -> insertR x t1
    -- Split on left-and-right subtrees of t1.
    (BinTree x l r, _) ->
      link x
           (hedgeUnion_LB_UB lo x  l t2)
           (hedgeUnion_LB    x     r t2)
{-# INLINABLE hedgeUnion_LB #-}

-- | Hedge union where we only add elements in second map if key is
-- strictly below a upper bound.
hedgeUnion_UB :: (IsBinTree c e, Ord e) => e -> c -> c -> c
hedgeUnion_UB hi t1 t2 =
  case (asBin t1, asBin t2) of
    (_, TipTree) -> t1
    (TipTree, _) -> fromMaybeS t2 (filterLt (compare hi) t2)
    -- Prune right tree.
    (_, BinTree x l _) | x >= hi -> hedgeUnion_UB hi t1 l
    -- Special case when t2 is a single element.
    (_, BinTree x (asBin -> TipTree) (asBin -> TipTree))  -> insertR x t1
    -- Split on left-and-right subtrees of t1.
    (BinTree x l r, _) ->
      link x
           (hedgeUnion_UB       x   l t2)
           (hedgeUnion_LB_UB x  hi  r t2)
{-# INLINABLE hedgeUnion_UB #-}

-- | Hedge union where we only add elements in second map if key is
-- strictly between a lower and upper bound.
hedgeUnion_LB_UB :: (IsBinTree c e, Ord e) => e -> e -> c -> c -> c
hedgeUnion_LB_UB lo hi t1 t2 =
  case (asBin t1, asBin t2) of
    (_, TipTree) -> t1
    -- Prune left tree.
    (_,   BinTree k _ r) | k <= lo -> hedgeUnion_LB_UB lo hi t1 r
    -- Prune right tree.
    (_,   BinTree k l _) | k >= hi -> hedgeUnion_LB_UB lo hi t1 l
    -- When t1 becomes empty (assumes lo <= k <= hi)
    (TipTree, BinTree x l r) ->
      case (filterGt (compare lo) l, filterLt (compare hi) r) of
        -- No variables in t2 were eliminated.
        (NothingS, NothingS) -> t2
        -- Relink t2 with filtered elements removed.
        (l',r') -> link x (fromMaybeS l l') (fromMaybeS r r')
    -- Special case when t2 is a single element.
    (_, BinTree x (asBin -> TipTree) (asBin -> TipTree)) -> insertR x t1
    -- Split on left-and-right subtrees of t1.
    (BinTree x l r, _) ->
      link x
           (hedgeUnion_LB_UB lo x  l t2)
           (hedgeUnion_LB_UB x  hi r t2)
{-# INLINABLE hedgeUnion_LB_UB #-}