------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Context
-- Copyright        : (c) Galois, Inc 2014-16
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- This module reexports either "Data.Parameterized.Context.Safe"
-- or "Data.Parameterized.Context.Unsafe" depending on the
-- the unsafe-operations compile-time flag.
--
-- It also defines some utility typeclasses for transforming
-- between curried and uncurried versions of functions over contexts.
------------------------------------------------------------------------

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Parameterized.Context
 (
#ifdef UNSAFE_OPS
   module Data.Parameterized.Context.Unsafe
#else
   module Data.Parameterized.Context.Safe
#endif
 , singleton
 , toVector
 , pattern (:>)
 , pattern Empty
   -- * Context extension and embedding utilities
 , CtxEmbedding(..)
 , ExtendContext(..)
 , ExtendContext'(..)
 , ApplyEmbedding(..)
 , ApplyEmbedding'(..)
 , identityEmbedding
 , extendEmbeddingRightDiff
 , extendEmbeddingRight
 , extendEmbeddingBoth
 , ctxeSize
 , ctxeAssignment

   -- * Static indexing and lenses for assignments
 , Idx
 , getCtx
 , setCtx
 , field
 , natIndex
 , natIndexProxy

   -- * Currying and uncurrying for assignments
 , CurryAssignment
 , CurryAssignmentClass(..)
 ) where

import Prelude hiding (null)

import GHC.TypeLits (Nat, type (-))

import Control.Lens hiding (Index, view, (:>), Empty)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

#ifdef UNSAFE_OPS
import Data.Parameterized.Context.Unsafe
#else
import Data.Parameterized.Context.Safe
#endif

import Data.Parameterized.TraversableFC

-- | Create a single element context.
singleton :: f tp -> Assignment f (EmptyCtx ::> tp)
singleton = (empty :>)

-- | Convert the assignment to a vector.
toVector :: Assignment f tps -> (forall tp . f tp -> e) -> V.Vector e
toVector a f = V.create $ do
  vm <- MV.new (sizeInt (size a))
  forIndexM (size a) $ \i -> do
    MV.write vm (indexVal i) (f (a ! i))
  return vm
{-# INLINABLE toVector #-}

--------------------------------------------------------------------------------
-- | Context embedding.

-- This datastructure contains a proof that the first context is
-- embeddable in the second.  This is useful if we want to add extend
-- an existing term under a larger context.

data CtxEmbedding (ctx :: Ctx k) (ctx' :: Ctx k)
  = CtxEmbedding { _ctxeSize       :: Size ctx'
                 , _ctxeAssignment :: Assignment (Index ctx') ctx
                 }

-- Alternate encoding?
-- data CtxEmbedding ctx ctx' where
--   EIdentity  :: CtxEmbedding ctx ctx
--   ExtendBoth :: CtxEmbedding ctx ctx' -> CtxEmbedding (ctx ::> tp) (ctx' ::> tp)
--   ExtendOne  :: CtxEmbedding ctx ctx' -> CtxEmbedding ctx (ctx' ::> tp)

ctxeSize :: Simple Lens (CtxEmbedding ctx ctx') (Size ctx')
ctxeSize = lens _ctxeSize (\s v -> s { _ctxeSize = v })

ctxeAssignment :: Lens (CtxEmbedding ctx1 ctx') (CtxEmbedding ctx2 ctx')
                       (Assignment (Index ctx') ctx1) (Assignment (Index ctx') ctx2)
ctxeAssignment = lens _ctxeAssignment (\s v -> s { _ctxeAssignment = v })

class ApplyEmbedding (f :: Ctx k -> *) where
  applyEmbedding :: CtxEmbedding ctx ctx' -> f ctx -> f ctx'

class ApplyEmbedding' (f :: Ctx k -> k' -> *) where
  applyEmbedding' :: CtxEmbedding ctx ctx' -> f ctx v -> f ctx' v

class ExtendContext (f :: Ctx k -> *) where
  extendContext :: Diff ctx ctx' -> f ctx -> f ctx'

class ExtendContext' (f :: Ctx k -> k' -> *) where
  extendContext' :: Diff ctx ctx' -> f ctx v -> f ctx' v

instance ApplyEmbedding' Index where
  applyEmbedding' ctxe idx = (ctxe ^. ctxeAssignment) ! idx

instance ExtendContext' Index where
  extendContext' = extendIndex'

-- -- This is the inefficient way of doing things.  A better way is to
-- -- just have a map between indices.
-- applyEmbedding :: CtxEmbedding ctx ctx'
--                -> Index ctx tp -> Index ctx' tp
-- applyEmbedding ctxe idx = (ctxe ^. ctxeAssignment) ! idx

identityEmbedding :: Size ctx -> CtxEmbedding ctx ctx
identityEmbedding sz = CtxEmbedding sz (generate sz id)

-- emptyEmbedding :: CtxEmbedding EmptyCtx EmptyCtx
-- emptyEmbedding = identityEmbedding knownSize

extendEmbeddingRightDiff :: forall ctx ctx' ctx''.
                            Diff ctx' ctx''
                            -> CtxEmbedding ctx ctx'
                            -> CtxEmbedding ctx ctx''
extendEmbeddingRightDiff diff (CtxEmbedding sz' assgn) = CtxEmbedding (extSize sz' diff) updated
  where
    updated :: Assignment (Index ctx'') ctx
    updated = fmapFC (extendIndex' diff) assgn

extendEmbeddingRight :: CtxEmbedding ctx ctx' -> CtxEmbedding ctx (ctx' ::> tp)
extendEmbeddingRight = extendEmbeddingRightDiff knownDiff

extendEmbeddingBoth :: forall ctx ctx' tp. CtxEmbedding ctx ctx' -> CtxEmbedding (ctx ::> tp) (ctx' ::> tp)
extendEmbeddingBoth ctxe = updated & ctxeAssignment %~ flip extend (nextIndex (ctxe ^. ctxeSize))
  where
    updated :: CtxEmbedding ctx (ctx' ::> tp)
    updated = extendEmbeddingRight ctxe

-- | Pattern synonym for the empty assignment
pattern Empty :: () => ctx ~ EmptyCtx => Assignment f ctx
pattern Empty <- (view -> AssignEmpty)
  where Empty = empty

infixl :>

-- | Pattern synonym for extending an assignment on the right
pattern (:>) :: () => ctx' ~ (ctx ::> tp) => Assignment f ctx -> f tp -> Assignment f ctx'
pattern (:>) a v <- (view -> AssignExtend a v)
  where a :> v = extend a v

-- The COMPLETE pragma was not defined until ghc 8.2.*
#if MIN_VERSION_base(4,10,0)
{-# COMPLETE (:>), Empty :: Assignment  #-}
#endif

--------------------------------------------------------------------------------
-- Static indexing based on type-level naturals

-- | Get an element from an 'Assignment' by zero-based, left-to-right position.
-- The position must be specified using @TypeApplications@ for the @n@ parameter.
getCtx :: forall n ctx f r. Idx n ctx r => Assignment f ctx -> f r
getCtx asgn = asgn ! natIndex @n

setCtx :: forall n ctx f r. Idx n ctx r => f r -> Assignment f ctx -> Assignment f ctx
setCtx = update (natIndex @n)

-- | Get a lens for an position in an 'Assignment' by zero-based, left-to-right position.
-- The position must be specified using @TypeApplications@ for the @n@ parameter.
field :: forall n ctx f r. Idx n ctx r => Lens' (Assignment f ctx) (f r)
field f = adjustM f (natIndex @n)

-- | Constraint synonym used for getting an 'Index' into a 'Ctx'.
-- @n@ is the zero-based, left-counted index into the list of types
-- @ctx@ which has the type @r@.
type Idx n ctx r = (ValidIx n ctx, Idx' (FromLeft ctx n) ctx r)

-- | Compute an 'Index' value for a particular position in a 'Ctx'. The
-- @TypeApplications@ extension will be needed to disambiguate the choice
-- of the type @n@.
natIndex :: forall n ctx r. Idx n ctx r => Index ctx r
natIndex = natIndex' @_ @(FromLeft ctx n)

-- | This version of 'natIndex' is suitable for use without the @TypeApplications@
-- extension.
natIndexProxy :: forall n ctx r proxy. Idx n ctx r => proxy n -> Index ctx r
natIndexProxy _ = natIndex @n

------------------------------------------------------------------------
-- Implementation
------------------------------------------------------------------------

-- | Class for computing 'Index' values for positions in a 'Ctx'.
class KnownContext ctx => Idx' (n :: Nat) (ctx :: Ctx k) (r :: k) | n ctx -> r where
  natIndex' :: Index ctx r

-- | Base-case
instance KnownContext xs => Idx' 0 (xs '::> x) x where
  natIndex' = lastIndex knownSize

-- | Inductive-step
instance {-# Overlaps #-} (KnownContext xs, Idx' (n-1) xs r) =>
  Idx' n (xs '::> x) r where

  natIndex' = skip (natIndex' @_ @(n-1))


--------------------------------------------------------------------------------
-- CurryAssignment

-- | This type family is used to define currying\/uncurrying operations
-- on assignments.  It is best understood by seeing its evaluation on
-- several examples:
--
-- > CurryAssignment EmptyCtx f x = x
-- > CurryAssignment (EmptyCtx ::> a) f x = f a -> x
-- > CurryAssignment (EmptyCtx ::> a ::> b) f x = f a -> f b -> x
-- > CurryAssignment (EmptyCtx ::> a ::> b ::> c) f x = f a -> f b -> f c -> x
type family CurryAssignment (ctx :: Ctx k) (f :: k -> *) (x :: *) :: * where
   CurryAssignment EmptyCtx    f x = x
   CurryAssignment (ctx ::> a) f x = CurryAssignment ctx f (f a -> x)

-- | This class implements two methods that witness the isomorphism between
--   curried and uncurried functions.
class CurryAssignmentClass (ctx :: Ctx k) where

  -- | Transform a function that accepts an assignment into one with a separate
  --   variable for each element of the assignment.
  curryAssignment   :: (Assignment f ctx -> x) -> CurryAssignment ctx f x

  -- | Transform a curried function into one that accepts an assignment value.
  uncurryAssignment :: CurryAssignment ctx f x -> (Assignment f ctx -> x)

instance CurryAssignmentClass EmptyCtx where
  curryAssignment k = k empty
  uncurryAssignment k _ = k

instance CurryAssignmentClass ctx => CurryAssignmentClass (ctx ::> a) where
  curryAssignment k = curryAssignment (\asgn a -> k (asgn :> a))
  uncurryAssignment k asgn =
    case view asgn of
      AssignExtend asgn' x -> uncurryAssignment k asgn' x
