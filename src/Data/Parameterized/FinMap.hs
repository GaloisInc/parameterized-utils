{-|
Copyright        : (c) Galois, Inc 2022

'FinMap' is a map with 'NatRepr' keys and a maximum size reflected in its
type. @'FinMap' n a@ can be used as a more space-efficient replacement for a
@'Data.Parameterized.Vector.Vector' n ('Maybe' a)@, or a replacement for an
@'Data.IntMap.IntMap' a@ where the maximum key (i.e., size) of the map can be
tracked statically.

This interface has two implementations:

* 'Data.Parameterized.FinMap.Unsafe.FinMap' is backed by an
  'Data.IntMap.IntMap', and must have a size of at most @'maxBound' :: 'Int'@.
  This module uses unsafe operations like 'Unsafe.Coerce.unsafeCoerce'
  internally for the sake of time and space efficiency.
* 'Data.Parameterized.FinMap.Safe.FinMap' is backed by an
  @'Data.Map.Map' ('Data.Parameterized.Fin.Fin' n)@. All of its functions are
  implemented using safe operations.

The implementation in 'Data.Parameterized.FinMap.Unsafe.FinMap' is property
tested against that in 'Data.Parameterized.FinMap.Safe.FinMap' to ensure
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
