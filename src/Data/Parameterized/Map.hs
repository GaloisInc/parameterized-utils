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

#if __GLASGOW_HASKELL__ >= 700
{-# INLINABLE lookup #-}
#else
{-# INLINE lookup #-}
#endif

elems :: MapF k a -> [Some a]
elems = foldrF (\e l -> Some e : l) []