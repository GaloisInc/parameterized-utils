{-|
Copyright        : (c) Galois, Inc 2022

'SizedMap' is a map with 'NatRepr' keys and a maximum size reflected in its
type. @'SizedMap' n a@ can be used as a more space-efficient replacement for a
@'Data.Parameterized.Vector.Vector' n ('Maybe' a)@, or a replacement for an
@'Data.IntMap.IntMap' a@ where the maximum key (i.e., size) of the map can be
tracked statically.

This interface has two implementations:

* 'Data.Parameterized.SizedMap.Unsafe.SizedMap' is backed by an
  'Data.IntMap.IntMap', and must have a size of at most @'maxBound' :: 'Int'@.
  This module uses unsafe operations like 'Unsafe.Coerce.unsafeCoerce'
  internally for the sake of time and space efficiency.
* 'Data.Parameterized.SizedMap.Safe.SizedMap' is backed by an
  @'Data.Map.Map' ('Data.Parameterized.Fin.Fin' n)@. All of its functions are
  implemented using safe operations.

The implementation in 'Data.Parameterized.SizedMap.Unsafe.SizedMap' is property
tested against that in 'Data.Parameterized.SizedMap.Safe.SizedMap' to ensure
they have the same behavior.

/W/ is used in big-O notations the same way as in the "Data.IntMap"
documentation.
-}

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Parameterized.SizedMap
  (
#ifdef UNSAFE_OPS
    module Data.Parameterized.SizedMap.Unsafe
#else
    module Data.Parameterized.SizedMap.Safe
#endif
  ) where

#ifdef UNSAFE_OPS
import Data.Parameterized.SizedMap.Unsafe
#else
import Data.Parameterized.SizedMap.Safe
#endif
