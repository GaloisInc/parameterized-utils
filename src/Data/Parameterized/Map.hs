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
  , insert
  , union
  , lookup
  , map
  , elems
  , module Data.Parameterized.Classes
  ) where

import Data.List (intercalate)
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

map :: (forall tp . f tp -> g tp) -> MapF ktp f -> MapF ktp g
map _ Tip = Tip
map f (Bin sx kx x l r) = Bin sx kx (f x) (map f l) (map f r)

#if __GLASGOW_HASKELL__ >= 709
{-# RULES
"map/coerce" map coerce = coerce
 #-}
#endif

instance FunctorF (MapF ktp) where
  fmapF = map

instance FoldableF (MapF ktp) where

  foldrF f z = go z
    where go z' Tip             = z'
          go z' (Bin _ _ x l r) = go (f x (go z' r)) l


empty :: MapF ktp rtp
empty = Tip

singleton :: k tp -> a tp -> MapF k a
singleton k x = Bin 1 k x Tip Tip

size :: MapF k a -> Int
size Tip              = 0
size (Bin sz _ _ _ _) = sz
{-# INLINE size #-}

delta,ratio :: Int
delta = 3
ratio = 2

-- balanceL is called when left subtree might have been inserted to or when
-- right subtree might have been deleted from.
balanceL :: k tp -> a tp -> MapF k a -> MapF k a -> MapF k a
balanceL k x l r = case r of
  Tip -> case l of
           Tip -> Bin 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin 2 k x l Tip
           (Bin _ lk lx Tip (Bin _ lrk lrx _ _)) -> Bin 3 lrk lrx (Bin 1 lk lx Tip Tip) (Bin 1 k x Tip Tip)
           (Bin _ lk lx ll@(Bin _ _ _ _ _) Tip) -> Bin 3 lk lx ll (Bin 1 k x Tip Tip)
           (Bin ls lk lx ll@(Bin lls _ _ _ _) lr@(Bin lrs lrk lrx lrl lrr))
             | lrs < ratio*lls -> Bin (1+ls) lk lx ll (Bin (1+lrs) k x lr Tip)
             | otherwise -> Bin (1+ls) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+size lrr) k x lrr Tip)

  (Bin rs _ _ _ _) -> case l of
           Tip -> Bin (1+rs) k x Tip r

           (Bin ls lk lx ll lr)
              | ls > delta*rs  -> case (ll, lr) of
                   (Bin lls _ _ _ _, Bin lrs lrk lrx lrl lrr)
                     | lrs < ratio*lls -> Bin (1+ls+rs) lk lx ll (Bin (1+rs+lrs) k x lr r)
                     | otherwise -> Bin (1+ls+rs) lrk lrx (Bin (1+lls+size lrl) lk lx ll lrl) (Bin (1+rs+size lrr) k x lrr r)
                   (_, _) -> error "Failure in Data.Map.balanceL"
              | otherwise -> Bin (1+ls+rs) k x l r
{-# NOINLINE balanceL #-}

-- balanceR is called when right subtree might have been inserted to or when
-- left subtree might have been deleted from.
balanceR :: k tp -> a tp -> MapF k a -> MapF k a -> MapF k a
balanceR k x l r = case l of
  Tip -> case r of
           Tip -> Bin 1 k x Tip Tip
           (Bin _ _ _ Tip Tip) -> Bin 2 k x Tip r
           (Bin _ rk rx Tip rr@(Bin _ _ _ _ _)) -> Bin 3 rk rx (Bin 1 k x Tip Tip) rr
           (Bin _ rk rx (Bin _ rlk rlx _ _) Tip) -> Bin 3 rlk rlx (Bin 1 k x Tip Tip) (Bin 1 rk rx Tip Tip)
           (Bin rs rk rx rl@(Bin rls rlk rlx rll rlr) rr@(Bin rrs _ _ _ _))
             | rls < ratio*rrs -> Bin (1+rs) rk rx (Bin (1+rls) k x Tip rl) rr
             | otherwise -> Bin (1+rs) rlk rlx (Bin (1+size rll) k x Tip rll) (Bin (1+rrs+size rlr) rk rx rlr rr)

  (Bin ls _ _ _ _) -> case r of
           Tip -> Bin (1+ls) k x l Tip

           (Bin rs rk rx rl rr)
              | rs > delta*ls  -> case (rl, rr) of
                   (Bin rls rlk rlx rll rlr, Bin rrs _ _ _ _)
                     | rls < ratio*rrs -> Bin (1+ls+rs) rk rx (Bin (1+ls+rls) k x l rl) rr
                     | otherwise -> Bin (1+ls+rs) rlk rlx (Bin (1+ls+size rll) k x l rll) (Bin (1+rrs+size rlr) rk rx rlr rr)
                   (_, _) -> error "Failure in Data.Map.balanceR"
              | otherwise -> Bin (1+ls+rs) k x l r
{-# NOINLINE balanceR #-}

link :: k tp -> a tp -> MapF k a -> MapF k a -> MapF k a
link kx x Tip r  = insertMin kx x r
link kx x l Tip  = insertMax kx x l
link kx x l@(Bin sizeL ky y ly ry) r@(Bin sizeR kz z lz rz)
  | delta*sizeL < sizeR  = balanceL kz z (link kx x l lz) rz
  | delta*sizeR < sizeL  = balanceR ky y ly (link kx x ry r)
  | otherwise            = Bin (sizeL + sizeR + 1) kx x l r

insertMax :: k tp -> a tp -> MapF k a -> MapF k a
insertMax kx x t =
  case t of
    Tip -> singleton kx x
    Bin _ ky y l r -> balanceR ky y l (insertMax kx x r)

insertMin :: k tp -> a tp -> MapF k a -> MapF k a
insertMin kx x t =
  case t of
    Tip -> singleton kx x
    Bin _ ky y l r -> balanceL ky y (insertMin kx x l) r

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
#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE insert #-}
#else
{-# INLINE insert #-}
#endif

foldrWithKey :: (forall s . k s -> a s -> b -> b) -> b -> MapF k a -> b
foldrWithKey f z = go z
  where
    go z' Tip = z'
    go z' (Bin _ kx x l r) = go (f kx x (go z' r)) l

instance (ShowF ktp, ShowF rtp) => Show (MapF ktp rtp) where
  show m = showMap showF showF m

showMap :: (forall tp . ktp tp -> String)
        -> (forall tp . rtp tp -> String)
        -> MapF ktp rtp
        -> String
showMap ppk ppv m = "{ " ++ intercalate "," l ++ " }"
  where l = foldrWithKey (\k a l0 -> (ppk k ++ " -> " ++ ppv a) : l0) [] m

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

-- Insert a new key and value in the map if it is not already present.
-- Used by `union`.
insertR :: OrdF k => k tp -> a tp -> MapF k a -> MapF k a
insertR  = \k v m -> seq k (go k v m)
  where
    go :: OrdF k => k tp -> a tp -> MapF k a -> MapF k a
    go kx x Tip = singleton kx x
    go kx x t@(Bin _ ky y l r) =
        case compareF kx ky of
          LTF -> balanceL ky y (go kx x l) r
          GTF -> balanceR ky y l (go kx x r)
          EQF -> t

{--------------------------------------------------------------------
  [filterGt b t] filter all keys >[b] from tree [t]
  [filterLt b t] filter all keys <[b] from tree [t]
--------------------------------------------------------------------}
filterGt :: OrdF k => MaybeS k -> MapF k v -> MapF k v
filterGt NothingS t = t
filterGt (JustS b) t = filter' b t
  where filter' _   Tip = Tip
        filter' b' (Bin _ kx x l r) =
          case compareF b' kx of
            LTF -> link kx x (filter' b' l) r
            EQF -> r
            GTF -> filter' b' r
{-# INLINABLE filterGt #-}

filterLt :: OrdF k => MaybeS k -> MapF k v -> MapF k v
filterLt NothingS t = t
filterLt (JustS b) t = filter' b t
  where filter' _   Tip = Tip
        filter' b' (Bin _ kx x l r) =
          case compareF kx b' of
            LTF -> link kx x l (filter' b' r)
            EQF -> l
            GTF -> filter' b' l
{-# INLINABLE filterLt #-}


data MaybeS (a :: k -> *) where
  NothingS :: MaybeS a
  JustS :: !(a tp) -> MaybeS a

trim :: OrdF k => MaybeS k -> MaybeS k -> MapF k a -> MapF k a
trim NothingS   NothingS   t = t
trim (JustS lk) NothingS   t = greater lk t
  where greater :: OrdF k => k tp -> MapF k a -> MapF k a
        greater lo (Bin _ k _ _ r) | k `leqF` lo = greater lo r
        greater _  t' = t'
trim NothingS   (JustS hk) t = lesser hk t
  where lesser :: OrdF k => k u -> MapF k a -> MapF k a
        lesser  hi (Bin _ k _ l _) | k `geqF` hi = lesser  hi l
        lesser  _  t' = t'
trim (JustS lk) (JustS hk) t = middle lk hk t
  where middle :: OrdF k => k u -> k v -> MapF k a -> MapF k a
        middle lo hi (Bin _ k _ _ r) | k `leqF` lo = middle lo hi r
        middle lo hi (Bin _ k _ l _) | k `geqF` hi = middle lo hi l
        middle _  _  t' = t'
{-# INLINABLE trim #-}

union :: OrdF k => MapF k a -> MapF k a -> MapF k a
union Tip t2  = t2
union t1 Tip  = t1
union t1 t2 = hedgeUnion NothingS NothingS t1 t2

-- left-biased hedge union
hedgeUnion :: OrdF a => MaybeS a -> MaybeS a -> MapF a b -> MapF a b -> MapF a b
hedgeUnion _   _   t1  Tip = t1
hedgeUnion blo bhi Tip (Bin _ kx x l r) = link kx x (filterGt blo l) (filterLt bhi r)
hedgeUnion _   _   t1  (Bin _ kx x Tip Tip) = insertR kx x t1  -- According to benchmarks, this special case increases
                                                              -- performance up to 30%. It does not help in difference or intersection.
hedgeUnion blo bhi (Bin _ kx x l r) t2 = link kx x (hedgeUnion blo bmi l (trim blo bmi t2))
                                                   (hedgeUnion bmi bhi r (trim bmi bhi t2))
  where bmi = JustS kx
{-# INLINABLE hedgeUnion #-}


elems :: MapF k a -> [Some a]
elems = foldrF (\e l -> Some e : l) []