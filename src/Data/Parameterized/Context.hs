------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Context
-- Description      : Finite dependent products
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module reexports either "Data.Parameterized.SafeContext"
-- or "Data.Parameterized.UnsafeContext" depending on the
-- the unsafe-operations compile-time flag.
{-# LANGUAGE CPP #-}
module Data.Parameterized.Context
(
#ifdef UNSAFE_OPS
module Data.Parameterized.UnsafeContext
#else
module Data.Parameterized.SafeContext
#endif
) where

#ifdef UNSAFE_OPS
import Data.Parameterized.UnsafeContext
#else
import Data.Parameterized.SafeContext
#endif
