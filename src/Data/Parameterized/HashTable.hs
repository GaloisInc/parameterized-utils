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
  , clear
  , HashableF(..)
  , Control.Monad.ST.RealWorld
  ) where

import Control.Applicative
import Control.Monad.ST
import qualified Data.HashTable.ST.Basic as H
import GHC.Prim (Any)
import Unsafe.Coerce

import Prelude hiding (lookup)

import Data.Parameterized.Classes
import Data.Parameterized.Some

-- | A hash table mapping nonces to values.
newtype HashTable s (key :: k -> *) (val :: k -> *)
      = HashTable (H.HashTable s (Some key) Any)

-- | Create a new empty table.
new :: ST s (HashTable s key val)
new = HashTable <$> H.new

-- | Lookup value of key in table.
lookup :: (HashableF key, TestEquality key)
       => HashTable s key val
       -> key tp
       -> ST s (Maybe (val tp))
lookup (HashTable h) k =
  fmap unsafeCoerce <$> H.lookup h (Some k)

-- | Insert new key and value mapping into table.
insert :: (HashableF key, TestEquality key)
       => HashTable s (key :: k -> *) (val :: k -> *)
       -> key tp
       -> val tp
       -> ST s ()
insert (HashTable h) k v = H.insert h (Some k) (unsafeCoerce v)

-- | Delete an element from the hash table.
delete :: (HashableF key, TestEquality key)
       => HashTable s (key :: k -> *) (val :: k -> *)
       -> key (tp :: k)
       -> ST s ()
delete (HashTable h) k = H.delete h (Some k)

clear :: (HashableF key, TestEquality key) => HashTable s (key :: k -> *) (val :: k -> *) -> ST s ()
clear (HashTable h) = H.mapM_ (\(k,_) -> H.delete h k) h

{-
-- | Delete an element from the hash table.
delete :: HashTable s val
       -> Nonce tp
       -> ST s ()
delete (HashTable h) k = H.delete h (Some k)
-}