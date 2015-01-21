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
-- A CoerceableF instance is needed to lookup values in these maps; it is
-- used to cast the element in the map (which is put inside an existential
-- datatype) to the requested output type.
------------------------------------------------------------------------
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

import Control.Applicative ((<$>))
import Data.List (intercalate)
import qualified Data.Map.Strict as Map
import Data.Maybe
import Prelude hiding (lookup, map)

import Data.Parameterized.Classes
import Data.Parameterized.Some

-- | A hash table mapping parameterid keys to values.
newtype MapF (ktp :: k -> *) (rtp :: k -> *) = MapF (Map.Map (Some ktp) (Some rtp))

{-# INLINE map #-}
map :: (forall tp . f tp -> g tp) -> MapF ktp f -> MapF ktp g
map f (MapF m) = MapF (fmap f' m)
  where f' (Some el) = Some (f el)

instance FunctorF (MapF ktp) where
  fmapF = map

instance (ShowF ktp, ShowF rtp) => Show (MapF ktp rtp) where
  show m = showMap showF showF m

showMap :: (forall tp . ktp tp -> String)
        -> (forall tp . rtp tp -> String)
        -> MapF ktp rtp
        -> String
showMap ppk ppv (MapF m) = "{ " ++ intercalate "," (ppEntry <$> Map.toList m) ++ " }"
  where ppEntry (Some k,Some v) = ppk k ++ " -> " ++ ppv v

empty :: MapF ktp rtp
empty = MapF Map.empty

insert :: OrdF ktp => ktp k -> rtp k -> MapF ktp rtp -> MapF ktp rtp
insert k v (MapF m) = MapF (Map.insert (Some k) (Some v) m)

-- | Lookup value in map.
lookup :: (CoerceableF rtp, OrdF ktp) => ktp k -> MapF ktp rtp -> Maybe (rtp k)
lookup k (MapF m) =
  case Map.lookup (Some k) m of
     Just (Some el) -> Just (coerceF el)
     Nothing -> Nothing

-- | Return value bound in map.
elems :: MapF ftp rtp -> [Some rtp]
elems (MapF m) = Map.elems m