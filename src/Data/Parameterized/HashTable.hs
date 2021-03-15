------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.HashTable
-- Description      : a hash table for parameterized keys and values
-- Copyright        : (c) Galois, Inc 2014-2019
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- This module provides a 'ST'-based hashtable for parameterized keys and values.
--
-- NOTE: This API makes use of 'unsafeCoerce' to implement the parameterized
-- hashtable abstraction.  This should be type-safe provided that the
-- 'TestEquality' instance on the key type is implemented soundly.
------------------------------------------------------------------------
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Trustworthy #-}
module Data.Parameterized.HashTable
  ( HashTable
  , new
  , newSized
  , clone
  , lookup
  , insert
  , member
  , delete
  , clear
  , Data.Parameterized.Classes.HashableF(..)
  , Control.Monad.ST.RealWorld
  ) where

import Control.Applicative
import Control.Monad.ST
import qualified Data.HashTable.ST.Basic as H
import Data.Kind
import GHC.Exts (Any)
import Unsafe.Coerce

import Prelude hiding (lookup)

import Data.Parameterized.Classes
import Data.Parameterized.Some

-- | A hash table mapping nonces to values.
newtype HashTable s (key :: k -> Type) (val :: k -> Type)
      = HashTable (H.HashTable s (Some key) Any)

-- | Create a new empty table.
new :: ST s (HashTable s key val)
new = HashTable <$> H.new

-- | Create a new empty table to hold 'n' elements.
newSized :: Int -> ST s (HashTable s k v)
newSized n = HashTable <$> H.newSized n

-- | Create a hash table that is a copy of the current one.
clone :: (HashableF key, TestEquality key)
      => HashTable s key val
      -> ST s (HashTable s key val)
clone (HashTable tbl) = do
  -- Create a new table
  r <- H.new
  -- Insert existing elements in
  H.mapM_ (uncurry (H.insert r)) tbl
  -- Return table
  return $! HashTable r

-- | Lookup value of key in table.
lookup :: (HashableF key, TestEquality key)
       => HashTable s key val
       -> key tp
       -> ST s (Maybe (val tp))
lookup (HashTable h) k = fmap unsafeCoerce <$> H.lookup h (Some k)
{-# INLINE lookup #-}

-- | Insert new key and value mapping into table.
insert :: (HashableF key, TestEquality key)
       => HashTable s (key :: k -> Type) (val :: k -> Type)
       -> key tp
       -> val tp
       -> ST s ()
insert (HashTable h) k v = H.insert h (Some k) (unsafeCoerce v)

-- | Return true if the key is in the hash table.
member :: (HashableF key, TestEquality key)
       => HashTable s (key :: k -> Type) (val :: k -> Type)
       -> key (tp :: k)
       -> ST s Bool
member (HashTable h) k = isJust <$> H.lookup h (Some k)

-- | Delete an element from the hash table.
delete :: (HashableF key, TestEquality key)
       => HashTable s (key :: k -> Type) (val :: k -> Type)
       -> key (tp :: k)
       -> ST s ()
delete (HashTable h) k = H.delete h (Some k)

clear :: (HashableF key, TestEquality key)
      => HashTable s (key :: k -> Type) (val :: k -> Type) -> ST s ()
clear (HashTable h) = H.mapM_ (\(k,_) -> H.delete h k) h
