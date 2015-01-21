------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.HashTable
-- Description      : ST-based hashtable for parameterized keys and values.
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module provides a ST-based hashtable for parameterized keys and values.
--
-- NOTE: This API makes use of unsafeCoerce to implement the parameterized
-- hashtable abstraction.  This should be typesafe provided the Nonce keys we
-- use have an unforgable connection to their claimed types.  See module
-- "Data.Parameterized.NonceGenerator" for comments about the safety
-- of that abstraction.
------------------------------------------------------------------------
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
module Data.Parameterized.HashTable
  ( HashTable
  , new
  , lookup
  , insert
  , delete
  , HashableF(..)
  ) where

import Control.Applicative
import Control.Monad.ST
import qualified Data.HashTable.ST.Basic as H
import GHC.Prim (Any)
import Unsafe.Coerce

import Prelude hiding (lookup)

import Data.Parameterized.Classes
import Data.Parameterized.NonceGenerator
import Data.Parameterized.Some

-- | A hash table mapping nonces to values.
newtype HashTable s (val :: k -> *)
      = HashTable (H.HashTable s (Some (Nonce :: k -> *)) Any)

-- | Create a new empty table.
new :: ST s (HashTable s val)
new = HashTable <$> H.new

-- | Lookup value of key in table.
lookup :: HashTable s val
       -> Nonce tp
       -> ST s (Maybe (val tp))
lookup (HashTable h) k =
  fmap unsafeCoerce <$> H.lookup h (Some k)

-- | Insert new key and value mapping into table.
insert :: HashTable s val
       -> Nonce tp
       -> val tp
       -> ST s ()
insert (HashTable h) k v = H.insert h (Some k) (unsafeCoerce v)


-- | Delete an element from the hash table.
delete :: HashTable s (val :: k -> *)
       -> Nonce (tp :: k)
       -> ST s ()
delete (HashTable h) k = H.delete h (Some k)


{-
-- | Delete an element from the hash table.
delete :: HashTable s val
       -> Nonce tp
       -> ST s ()
delete (HashTable h) k = H.delete h (Some k)
-}