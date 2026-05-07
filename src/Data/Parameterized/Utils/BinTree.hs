{-|
Description      : Utilities for balanced binary trees.
Copyright        : (c) Galois, Inc 2014-2019
Maintainer       : Joe Hendrix <jhendrix@galois.com>
-}
{-# LANGUAGE Safe #-}
module Data.Parameterized.Utils.BinTree
  ( MaybeS(..)
  , fromMaybeS
  , Updated(..)
  , updatedValue
  , TreeApp(..)
  , IsBinTree(..)
  , balanceL
  , balanceR
  , glue
  , merge
  , filterGt
  , filterLt
  , insert
  , delete
  , union
  , link
  , PairS(..)
  ) where

import Data.Parameterized.Utils.BinTree.Internal
