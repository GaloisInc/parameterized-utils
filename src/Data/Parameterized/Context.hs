------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Context
-- Copyright        : (c) Galois, Inc 2014-16
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- This module reexports either "Data.Parameterized.SafeContext"
-- or "Data.Parameterized.UnsafeContext" depending on the
-- the unsafe-operations compile-time flag.
--
-- It also defines some utility typeclasses for transforming
-- between curried and uncurried versions of functions over contexts.
------------------------------------------------------------------------

{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE Trustworthy #-}
module Data.Parameterized.Context
 (
#ifdef UNSAFE_OPS
   module Data.Parameterized.UnsafeContext
#else
   module Data.Parameterized.SafeContext
#endif
 , singleton
 , toVector
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

   -- * Currying and uncurrying for assignments
 , CurryAssignment
 , CurryAssignmentClass(..)
 ) where

import Control.Lens hiding (Index, view)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

#ifdef UNSAFE_OPS
import Data.Parameterized.UnsafeContext
#else
import Data.Parameterized.SafeContext
#endif

import Data.Parameterized.TraversableFC


-- | Create a single element context.
singleton :: f tp -> Assignment f (EmptyCtx ::> tp)
singleton = (empty %>)

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
  curryAssignment k = curryAssignment (\asgn a -> k (asgn %> a))
  uncurryAssignment k asgn =
    case view asgn of
      AssignExtend asgn' x -> uncurryAssignment k asgn' x
