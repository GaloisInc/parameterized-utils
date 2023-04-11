{-|
Description : Decideable equality (i.e. evidence of non-equality) on type families
Copyright   : (c) Galois, Inc 2014-2019
Maintainer  : Langston Barrett <langston@galois.com>

This defines a class @DecidableEq@, which represents decidable equality on a
type family.

This is different from GHC's @TestEquality@ in that it provides evidence
of non-equality. In fact, it is a superclass of @TestEquality@.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE Safe #-}
#if __GLASGOW_HASKELL__ < 806
{-# LANGUAGE TypeInType #-}
#endif
module Data.Parameterized.DecidableEq
  ( DecidableEq(..)
  ) where

import Data.Void (Void)
import Data.Type.Equality ((:~:))

-- | Decidable equality.
class DecidableEq f where
  decEq :: f a -> f b -> Either (a :~: b) ((a :~: b) -> Void)

-- TODO: instances for sums, products of types with decidable equality

-- import Data.Type.Equality ((:~:), TestEquality(..))
-- instance (DecidableEq f) => TestEquality f where
--   testEquality a b =
--     case decEq a b of
--       Left  prf -> Just prf
--       Right _   -> Nothing
