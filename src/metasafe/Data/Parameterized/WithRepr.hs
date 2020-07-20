{-# LANGUAGE CPP #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-|
Copyright        : (c) Galois, Inc 2019

This module declares a class with a single method that can be used to
derive a 'KnownRepr' constraint from an explicit 'Repr' argument.
Clients of this method need only create an empty instance. The default
implementation suffices.

For example, suppose we have defined a 'Repr' type for 'Peano' numbers:

@
data Peano = Z | S Peano

data PeanoRepr p where
    ZRepr :: PeanoRepr Z
    SRepr :: PeanoRepr p -> PeanoRepr (S p)

-- KnownRepr instances
@

Then the instance for this class
@
instance IsRepr PeanoRepr
@

means that functions with 'KnownRepr' constraints can be used after
pattern matching.

@
f :: KnownRepr PeanoRepr a => ...

example :: PeanoRepr n -> ...
example ZRepr = ...
example (SRepr (pm::PeanoRepr m)) = ... withRepr pm f ...
@


NOTE: The type 'f' must be a *singleton* type--- i.e.  for a given
type 'a' there should be only one value that inhabits 'f a'. If that
is not the case, this operation can be used to subvert coherence.

Credit: the unsafe implementation of 'withRepr' is taken from the
'withSingI' function in the singletons library
<http://hackage.haskell.org/package/singletons-2.5.1/>.  Packaging
this method in a class here makes it more flexible---we do not have to
define a dedicated 'Sing' type, but can use any convenient singleton
as a 'Repr'.

NOTE: if this module is compiled without UNSAFE_OPS, the default
method will not be available.

-}
module Data.Parameterized.WithRepr(IsRepr(..)) where

import Data.Parameterized.Classes

#ifdef UNSAFE_OPS
import Data.Constraint(Dict(..))
import Unsafe.Coerce(unsafeCoerce)

import Data.Parameterized.NatRepr (NatRepr)
import Data.Parameterized.SymbolRepr (SymbolRepr)
import Data.Parameterized.Peano (PeanoRepr)
import Data.Parameterized.Context(Assignment)
import Data.Parameterized.List(List)
#else
import Data.Parameterized.Peano (PeanoRepr,PeanoView(..))
#endif
import Data.Parameterized.BoolRepr

-- | Turn an explicit Repr value into an implict KnownRepr constraint
class IsRepr (f :: k -> *) where

  withRepr :: f a -> (KnownRepr f a => r) -> r

#ifdef UNSAFE_OPS
  withRepr si r = case reprInstance si of
                     Dict -> r

reprInstance :: forall f a . IsRepr f => f a -> Dict (KnownRepr f a)
reprInstance s = with_repr Dict
   where
     with_repr :: (KnownRepr f a => Dict (KnownRepr f a)) -> Dict (KnownRepr f a)
     with_repr si = unsafeCoerce (Don'tInstantiate si) s

newtype DI f a = Don'tInstantiate (KnownRepr f a => Dict (KnownRepr f a))
#endif


------------------------------------
-- Instances for types defined in parameterized-utils

#ifdef UNSAFE_OPS
instance IsRepr NatRepr
instance IsRepr SymbolRepr
instance IsRepr PeanoRepr
instance IsRepr BoolRepr
instance IsRepr f => IsRepr (List f)
instance IsRepr f => IsRepr (Assignment f)
#else
-- awful, slow implementation for PeanoRepr
instance IsRepr PeanoRepr where
  withRepr ZRepr f     = f
  withRepr (SRepr m) f = withRepr m f

instance IsRepr BoolRepr where
  withRepr TrueRepr f = f
  withRepr FalseRepr f = f
#endif
