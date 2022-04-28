{-|
Copyright        : (c) Galois, Inc 2022

@'FinMap' n a@ conceptually (see NOTE) a map with @'Data.Parameterized.Fin.Fin'
n@ keys, implying a maximum size of @n@. Here's how 'FinMap' compares to other
map-like types:

* @'FinMap' n a@ is conceptually isomorphic to a
  @'Data.Parameterized.Vector' n ('Maybe' a)@, but can be more space-efficient
  especially if @n@ is large and the vector is populated with a small number of
  'Just' values.
* @'FinMap'@ is less general than 'Data.Map.Map', because it has a fixed key
  type (@'Data.Parameterized.Fin.Fin' n@).
* @'FinMap' n a@ is similar to @'Data.IntMap.IntMap' a@, but it provides a
  static guarantee of a maximum size, and its operations (such as 'size') allow
  the recovery of more type-level information.
* @'FinMap'@ is dissimilar from "Data.Parameterized.Map.MapF" in that neither
  the key nor value type of 'FinMap' is parameterized.

The type parameter @n@ doesn't track the /current/ number of key-value pairs in
a @'FinMap' n@ (i.e., the size of the map), but rather /an upper bound/.
'insert' and 'delete' don't alter @n@, whereas 'incMax' does - despite the fact
that it has no effect on the keys and values in the 'FinMap'.

The 'FinMap' interface has two implementations:

* The implementation in "Data.Parameterized.FinMap.Unsafe" is backed by an
  'Data.IntMap.IntMap', and must have a size of at most @'maxBound' :: 'Int'@.
  This module uses unsafe operations like 'Unsafe.Coerce.unsafeCoerce'
  internally for the sake of time and space efficiency.
* The implementation in "Data.Parameterized.FinMap.Safe" is backed by an
  @'Data.Map.Map' ('Data.Parameterized.Fin.Fin' n)@. All of its functions are
  implemented using safe operations.

The implementation in 'Data.Parameterized.FinMap.Unsafe.FinMap' is property
tested against that in 'Data.Parameterized.FinMap.Safe.FinMap' to ensure
they have the same behavior.

In this documentation, /W/ is used in big-O notations the same way as in the
"Data.IntMap" documentation.

NOTE: Where the word "conceptually" is used, it implies that this correspondence
is not literally true, but is true modulo some details such as differences
between bounded types like 'Int' and unbounded types like 'Integer'.

Several of the functions in both implementations are marked @INLINE@ or
@INLINABLE@. There are three reasons for this:

* Some of these just have very small definitions and so inlining is likely more
  beneficial than harmful.
* Some participate in @RULES@ relevant to functions used in their
  implementations.
* They are thin wrappers (often just newtype wrappers) around functions marked
  @INLINE@, which should therefore also be inlined.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Parameterized.FinMap
  (
#ifdef UNSAFE_OPS
    module Data.Parameterized.FinMap.Unsafe
#else
    module Data.Parameterized.FinMap.Safe
#endif
  ) where

#ifdef UNSAFE_OPS
import Data.Parameterized.FinMap.Unsafe
#else
import Data.Parameterized.FinMap.Safe
#endif
