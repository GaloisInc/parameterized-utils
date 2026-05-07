{-|
Module : Data.Parameterized.SmallArrayF
Copyright : (c) Galois, Inc 2026
Maintainer : Langston Barrett <langston@galois.com>

A type-parameterized, fixed-size, heterogeneous container indexed by
a type-level 'Data.Parameterized.Ctx.Ctx'.

Compared with 'Data.Parameterized.Context.Assignment', 'SmallArrayF'
trades \(O(1)\)-amortized 'extend' for \(O(1)\) indexing and \(O(n)\)
'extend'/'update'.  Intended for small, read-heavy use cases such as
machine register files.  For incremental construction, build an
'Data.Parameterized.Context.Assignment' and convert via
'fromAssignment' at the boundary.
-}

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Parameterized.SmallArrayF
  ( SmallArrayF
    -- * Construction
  , empty
  , singleton
  , from2
  , from3
  , from4
  , from5
  , from6
  , from7
  , from8
  , from9
  , generate
  , generateA
  , generateST
  , generateIO
    -- * Query
  , (!)
  , size
    -- * Modification
  , update
  , adjust
  , adjustM
  , extend
  , unextend
    -- * Combine
  , zipWithFC
  , zipWithMFC
  , zipWithMFCST
  , zipWithMFCIO
  , append
    -- * Subarray
  , take
  , drop

    -- * Traversal
  , traverseFCST
  , traverseFCIO
  , itraverseFCST
  , itraverseFCIO

    -- * Conversion
  , fromAssignment
  , toAssignment
  ) where

import           Prelude hiding (drop, take)

import           Control.DeepSeq (NFData(rnf))
import           Control.Monad.IO.Class (MonadIO(liftIO))
import           Control.Monad.ST (ST, runST, stToIO)
import           Data.Functor.Identity (Identity(Identity, runIdentity))
import           Data.Kind (Type)
import           Data.List (intercalate)
import qualified GHC.Exts as Exts
import           GHC.Exts (Any, Int(I#), Int#, isTrue#, (>=#), (/=#), (+#), (-#))
import           GHC.ST (ST(ST))
import           Unsafe.Coerce (unsafeCoerce)

import qualified Lens.Micro as Lens

import           Data.Parameterized.Axiom (unsafeAxiom)
import           Data.Parameterized.Classes
import           Data.Parameterized.Ctx (Ctx, EmptyCtx, type (::>), type (<+>))
import           Data.Parameterized.Context (Assignment, Index, Size)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.TraversableFC.WithIndex

------------------------------------------------------------------------
-- Representation

-- | A container holding a value @f tp@ at each position prescribed by
-- the type-level context @ctx@.
--
-- Indexing matches 'Data.Parameterized.Context.Assignment': the @i@th
-- 'Index' refers to the @i@th element left-to-right.
data SmallArrayF (f :: k -> Type) (ctx :: Ctx k)
  = SmallArrayF (Exts.SmallArray# (f Any))

type role SmallArrayF nominal nominal

------------------------------------------------------------------------
-- Primop wrappers
--
-- SmallArray# and SmallMutableArray# are unlifted, so we wrap them in
-- ST-friendly combinators here rather than inline at every use site.

-- A lifted wrapper around SmallMutableArray# so it can flow through ST.
data MutArr s (f :: k -> Type) = MutArr (Exts.SmallMutableArray# s (f Any))

newMut# :: Int# -> ST s (MutArr s f)
newMut# n = ST $ \s ->
  case Exts.newSmallArray# n uninitialized s of
    (# s', m #) -> (# s', MutArr m #)
  where
    uninitialized :: f Any
    uninitialized = error "Data.Parameterized.SmallArrayF: uninitialized slot"
{-# INLINE newMut# #-}

writeMut# :: MutArr s f -> Int# -> f Any -> ST s ()
writeMut# (MutArr m) i x = ST $ \s ->
  case Exts.writeSmallArray# m i x s of
    s' -> (# s', () #)
{-# INLINE writeMut# #-}

freezeMut :: MutArr s f -> ST s (SmallArrayF f ctx)
freezeMut (MutArr m) = ST $ \s ->
  case Exts.unsafeFreezeSmallArray# m s of
    (# s', arr #) -> (# s', SmallArrayF arr #)
{-# INLINE freezeMut #-}

-- | Copy @n@ elements from a frozen array into a mutable array,
-- starting at offset 0 in both.
copyInto# :: Exts.SmallArray# (f Any) -> MutArr s f -> Int# -> ST s ()
copyInto# src (MutArr dst) n = ST $ \s ->
  case Exts.copySmallArray# src 0# dst 0# n s of
    s' -> (# s', () #)
{-# INLINE copyInto# #-}

-- | Copy @n@ elements from a frozen array starting at @srcOff@ into a
-- mutable array starting at @dstOff@.
copyIntoAt# ::
  Exts.SmallArray# (f Any) ->
  Int# ->
  MutArr s f ->
  Int# ->
  Int# ->
  ST s ()
copyIntoAt# src srcOff (MutArr dst) dstOff n = ST $ \s ->
  case Exts.copySmallArray# src srcOff dst dstOff n s of
    s' -> (# s', () #)
{-# INLINE copyIntoAt# #-}

-- | Read a value from a frozen array at the given unboxed offset.
index# :: Exts.SmallArray# (f Any) -> Int# -> f Any
index# arr i = case Exts.indexSmallArray# arr i of (# x #) -> x
{-# INLINE index# #-}

-- | Number of elements in a frozen array, as an unboxed 'Int#'.
size# :: Exts.SmallArray# (f Any) -> Int#
size# arr = Exts.sizeofSmallArray# arr
{-# INLINE size# #-}

------------------------------------------------------------------------
-- Iteration and folds over raw arrays

-- | @forN_ n k@ executes @k 0#@, @k 1#@, ..., @k (n-1)#@ in order.
forN_ :: Applicative m => Int# -> (Int# -> m ()) -> m ()
forN_ n k = go 0#
  where
    go i
      | isTrue# (i >=# n) = pure ()
      | otherwise = k i *> go (i +# 1#)
{-# INLINE forN_ #-}

-- | Like 'forN_', but passes a type-safe 'Index' at each step.
forIndices_ ::
  Applicative m =>
  Int# ->
  (forall tp. Index ctx tp -> m ()) ->
  m ()
forIndices_ n k =
  -- SAFETY: offsets are in @[0, n)@, matching positions in @ctx@.
  forN_ n (\i -> k (unsafeMakeIndex (I# i)))
{-# INLINE forIndices_ #-}

-- | Right-fold over the elements of a frozen array.
foldrArr :: (f Any -> b -> b) -> b -> Exts.SmallArray# (f Any) -> b
foldrArr h = ifoldrArr (\_ x -> h x)
{-# INLINE foldrArr #-}

-- | Right-fold over a frozen array with the element's integer offset.
ifoldrArr :: (Int -> f Any -> b -> b) -> b -> Exts.SmallArray# (f Any) -> b
ifoldrArr h z arr = go 0#
  where
    n = size# arr
    go i
      | isTrue# (i >=# n) = z
      | otherwise = h (I# i) (index# arr i) (go (i +# 1#))
{-# INLINE ifoldrArr #-}

-- | Right-fold over a frozen array with a type-safe 'Index' and the
-- element coerced to match.
foldrArrWithIndex ::
  (forall tp. Index ctx tp -> f tp -> b -> b) ->
  b ->
  Exts.SmallArray# (f Any) ->
  b
foldrArrWithIndex h =
  -- SAFETY: slot @i@ was written as @f tp@ for the @tp@ at position
  -- @i@ in @ctx@; the 'Index' witnesses that @tp@.
  ifoldrArr (\i x -> h (unsafeMakeIndex i) (unsafeFromAny x))
{-# INLINE foldrArrWithIndex #-}

-- | Strict left-fold over the elements of a frozen array.
foldlArr' :: (b -> f Any -> b) -> b -> Exts.SmallArray# (f Any) -> b
foldlArr' h z0 arr = go 0# z0
  where
    n = size# arr
    go i !z
      | isTrue# (i >=# n) = z
      | otherwise = go (i +# 1#) (h z (index# arr i))
{-# INLINE foldlArr' #-}

-- | Build a 'SmallArrayF' of the given size by writing the given list
-- of values in order.  The list must have exactly @n@ elements;
-- shorter lists leave trailing slots as thunks that throw when read,
-- and longer lists are truncated, so callers must ensure the length
-- matches.
unsafeFromListN# :: Int# -> [f Any] -> SmallArrayF f ctx
unsafeFromListN# n ys0 = runST $ do
  mut <- newMut# n
  let loop _ []     = pure ()
      loop i (y:yt) = writeMut# mut i y *> loop (i +# 1#) yt
  loop 0# ys0
  freezeMut mut
{-# INLINE unsafeFromListN# #-}

unsafeFromListN :: Int -> [f Any] -> SmallArrayF f ctx
unsafeFromListN (I# n) = unsafeFromListN# n
{-# INLINE unsafeFromListN #-}

------------------------------------------------------------------------
-- Payload coercions
--
-- The array stores values as @f Any@. Callers that supply a concrete
-- @tp@ via an @Index ctx tp@ recover the real type via these coercions.
-- The type role @nominal nominal@ on 'SmallArrayF' prevents users from
-- conflating different @f@s or @ctx@s via 'coerce'.

toAny :: f tp -> f Any
toAny = unsafeCoerce
{-# INLINE toAny #-}

unsafeFromAny :: f Any -> f tp
unsafeFromAny = unsafeCoerce
{-# INLINE unsafeFromAny #-}


------------------------------------------------------------------------
-- Construction

-- | \(O(1)\).  The empty container.
empty :: SmallArrayF f EmptyCtx
empty = runST $ do
  mut <- newMut# 0#
  freezeMut mut

-- | \(O(1)\).  A container with a single element.
singleton :: f tp -> SmallArrayF f (EmptyCtx ::> tp)
singleton x = runST $ do
  mut <- newMut# 1#
  writeMut# mut 0# (toAny x)
  freezeMut mut

-- | \(O(1)\).  A container with two elements.
from2 ::
  f t0 ->
  f t1 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1)
from2 x0 x1 = runST $ do
  mut <- newMut# 2#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  freezeMut mut

-- | \(O(1)\).  A container with three elements.
from3 ::
  f t0 ->
  f t1 ->
  f t2 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1 ::> t2)
from3 x0 x1 x2 = runST $ do
  mut <- newMut# 3#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  writeMut# mut 2# (toAny x2)
  freezeMut mut

-- | \(O(1)\).  A container with four elements.
from4 ::
  f t0 ->
  f t1 ->
  f t2 ->
  f t3 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1 ::> t2 ::> t3)
from4 x0 x1 x2 x3 = runST $ do
  mut <- newMut# 4#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  writeMut# mut 2# (toAny x2)
  writeMut# mut 3# (toAny x3)
  freezeMut mut

-- | \(O(1)\).  A container with five elements.
from5 ::
  f t0 ->
  f t1 ->
  f t2 ->
  f t3 ->
  f t4 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1 ::> t2 ::> t3 ::> t4)
from5 x0 x1 x2 x3 x4 = runST $ do
  mut <- newMut# 5#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  writeMut# mut 2# (toAny x2)
  writeMut# mut 3# (toAny x3)
  writeMut# mut 4# (toAny x4)
  freezeMut mut

-- | \(O(1)\).  A container with six elements.
from6 ::
  f t0 ->
  f t1 ->
  f t2 ->
  f t3 ->
  f t4 ->
  f t5 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1 ::> t2 ::> t3 ::> t4 ::> t5)
from6 x0 x1 x2 x3 x4 x5 = runST $ do
  mut <- newMut# 6#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  writeMut# mut 2# (toAny x2)
  writeMut# mut 3# (toAny x3)
  writeMut# mut 4# (toAny x4)
  writeMut# mut 5# (toAny x5)
  freezeMut mut

-- | \(O(1)\).  A container with seven elements.
from7 ::
  f t0 ->
  f t1 ->
  f t2 ->
  f t3 ->
  f t4 ->
  f t5 ->
  f t6 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1 ::> t2 ::> t3 ::> t4 ::> t5 ::> t6)
from7 x0 x1 x2 x3 x4 x5 x6 = runST $ do
  mut <- newMut# 7#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  writeMut# mut 2# (toAny x2)
  writeMut# mut 3# (toAny x3)
  writeMut# mut 4# (toAny x4)
  writeMut# mut 5# (toAny x5)
  writeMut# mut 6# (toAny x6)
  freezeMut mut

-- | \(O(1)\).  A container with eight elements.
from8 ::
  f t0 ->
  f t1 ->
  f t2 ->
  f t3 ->
  f t4 ->
  f t5 ->
  f t6 ->
  f t7 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1 ::> t2 ::> t3 ::> t4 ::> t5 ::> t6 ::> t7)
from8 x0 x1 x2 x3 x4 x5 x6 x7 = runST $ do
  mut <- newMut# 8#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  writeMut# mut 2# (toAny x2)
  writeMut# mut 3# (toAny x3)
  writeMut# mut 4# (toAny x4)
  writeMut# mut 5# (toAny x5)
  writeMut# mut 6# (toAny x6)
  writeMut# mut 7# (toAny x7)
  freezeMut mut

-- | \(O(1)\).  A container with nine elements.
from9 ::
  f t0 ->
  f t1 ->
  f t2 ->
  f t3 ->
  f t4 ->
  f t5 ->
  f t6 ->
  f t7 ->
  f t8 ->
  SmallArrayF f (EmptyCtx ::> t0 ::> t1 ::> t2 ::> t3 ::> t4 ::> t5 ::> t6 ::> t7 ::> t8)
from9 x0 x1 x2 x3 x4 x5 x6 x7 x8 = runST $ do
  mut <- newMut# 9#
  writeMut# mut 0# (toAny x0)
  writeMut# mut 1# (toAny x1)
  writeMut# mut 2# (toAny x2)
  writeMut# mut 3# (toAny x3)
  writeMut# mut 4# (toAny x4)
  writeMut# mut 5# (toAny x5)
  writeMut# mut 6# (toAny x6)
  writeMut# mut 7# (toAny x7)
  writeMut# mut 8# (toAny x8)
  freezeMut mut

-- | \(O(n)\).  Build a 'SmallArrayF' by applying the supplied function
-- at each index.
generate ::
  forall k (f :: k -> Type) (ctx :: Ctx k).
  Size ctx ->
  (forall tp. Index ctx tp -> f tp) ->
  SmallArrayF f ctx
generate sz fn = runST $ do
  let !(I# n) = Ctx.sizeInt sz
  mut <- newMut# n
  forIndices_ n $ \idx ->
    let !(I# i#) = Ctx.indexVal idx
    in writeMut# mut i# (toAny (fn idx))
  freezeMut mut
{-# INLINE generate #-}

-- | \(O(n)\) plus the cost of the @f@-actions.  Build a 'SmallArrayF'
-- effectfully under an 'Applicative' constraint.
generateA ::
  forall k (f :: k -> Type) (ctx :: Ctx k) m.
  Applicative m =>
  Size ctx ->
  (forall tp. Index ctx tp -> m (f tp)) ->
  m (SmallArrayF f ctx)
generateA sz fn = unsafeFromListN (Ctx.sizeInt sz) <$> xs
  where
    xs :: m [f Any]
    xs = Ctx.forIndexRange 0 sz step (pure [])
      where
        step :: Index ctx tp -> m [f Any] -> m [f Any]
        step idx rest = (:) <$> (toAny <$> fn idx) <*> rest
{-# INLINE [1] generateA #-}

{-# RULES "generateA/Identity"
    forall sz (fn :: forall tp. Index ctx tp -> Identity (f tp)).
    generateA sz fn = Identity (generate sz (runIdentity . fn)) #-}

-- | \(O(n)\) plus the cost of the @f@-actions.  Build a 'SmallArrayF'
-- in 'ST'.
--
-- Unlike 'generateA', this writes each result directly into the
-- target array as it is produced, so no intermediate list is
-- allocated.
generateST ::
  forall k (f :: k -> Type) (ctx :: Ctx k) s.
  Size ctx ->
  (forall tp. Index ctx tp -> ST s (f tp)) ->
  ST s (SmallArrayF f ctx)
generateST sz fn = do
  let !(I# n) = Ctx.sizeInt sz
  mut <- newMut# n
  forIndices_ n $ \idx -> do
    x <- fn idx
    let !(I# i#) = Ctx.indexVal idx
    writeMut# mut i# (toAny x)
  freezeMut mut
{-# INLINE generateST #-}

-- | \(O(n)\) plus the cost of the @f@-actions.  Build a 'SmallArrayF'
-- in an 'IO'-based monad.
generateIO ::
  forall k (f :: k -> Type) (ctx :: Ctx k) m.
  MonadIO m =>
  Size ctx ->
  (forall tp. Index ctx tp -> m (f tp)) ->
  m (SmallArrayF f ctx)
generateIO sz fn = do
  let !(I# n) = Ctx.sizeInt sz
  mut <- liftIO (stToIO (newMut# n))
  forIndices_ n $ \idx -> do
    x <- fn idx
    let !(I# i#) = Ctx.indexVal idx
    liftIO (stToIO (writeMut# mut i# (toAny x)))
  liftIO (stToIO (freezeMut mut))
{-# SPECIALIZE generateIO ::
      Size ctx
   -> (forall tp. Index ctx tp -> IO (f tp))
   -> IO (SmallArrayF f ctx) #-}

unsafeMakeIndex :: Int -> Index ctx tp
unsafeMakeIndex = unsafeCoerce
{-# INLINE unsafeMakeIndex #-}

------------------------------------------------------------------------
-- Size

-- | \(O(1)\).  The number of elements in the container.
size :: SmallArrayF f ctx -> Size ctx
size (SmallArrayF arr) =
  -- SAFETY: 'Size' is a newtype over 'Int' and the array length equals
  -- the number of positions in @ctx@ by construction.
  unsafeCoerce (I# (size# arr))
{-# INLINE [1] size #-}

------------------------------------------------------------------------
-- Indexing

-- | \(O(1)\).  @a ! i@ is the element at position @i@ in @a@.
(!) :: SmallArrayF f ctx -> Index ctx tp -> f tp
(!) (SmallArrayF arr) idx =
  -- SAFETY: the slot at @indexVal idx@ was written as an @f tp@ when
  -- the array was constructed, so coercing back to @f tp@ is sound.
  let !(I# i#) = Ctx.indexVal idx
  in unsafeFromAny (index# arr i#)
{-# INLINE (!) #-}

infixl 9 !

------------------------------------------------------------------------
-- Modification

-- | \(O(n)\).  Replace the element at the given index.  Allocates a
-- fresh array and copies all elements into it.
update :: Index ctx tp -> f tp -> SmallArrayF f ctx -> SmallArrayF f ctx
update idx x (SmallArrayF src) = runST $ do
  let n = size# src
      !(I# i#) = Ctx.indexVal idx
  mut <- newMut# n
  copyInto# src mut n
  writeMut# mut i# (toAny x)
  freezeMut mut

-- | \(O(n)\).  Apply a function at the given index.  Allocates a fresh
-- array (inherits the cost of 'update').
adjust ::
  (f tp -> f tp) ->
  Index ctx tp ->
  SmallArrayF f ctx ->
  SmallArrayF f ctx
adjust f idx a = runIdentity (adjustM (Identity . f) idx a)
{-# INLINE adjust #-}

-- | \(O(n)\) plus the cost of the @m@-action.  Apply an effectful
-- function at the given index.  Allocates a fresh array (inherits the
-- cost of 'update').
adjustM ::
  Functor m =>
  (f tp -> m (f tp)) ->
  Index ctx tp ->
  SmallArrayF f ctx ->
  m (SmallArrayF f ctx)
adjustM f idx a = (\x -> update idx x a) <$> f (a ! idx)
{-# INLINE adjustM #-}
-- For 'adjust':
{-# SPECIALIZE adjustM ::
      (f tp -> Identity (f tp))
   -> Index ctx tp
   -> SmallArrayF f ctx
   -> Identity (SmallArrayF f ctx) #-}

-- | \(O(n)\).  Append a new element on the right.  Allocates a fresh
-- array of size n+1.
extend :: SmallArrayF f ctx -> f tp -> SmallArrayF f (ctx ::> tp)
extend (SmallArrayF src) x = runST $ do
  let n = size# src
  mut <- newMut# (n +# 1#)
  copyInto# src mut n
  writeMut# mut n (toAny x)
  freezeMut mut

-- | \(O(n)\).  Split off the last element.  Allocates a fresh array of
-- size @n - 1@.
unextend :: SmallArrayF f (ctx ::> tp) -> (SmallArrayF f ctx, f tp)
unextend (SmallArrayF arr) = runST $ do
  let n = size# arr
      m = n -# 1#
  mut <- newMut# m
  copyIntoAt# arr 0# mut 0# m
  frozen <- freezeMut mut
  -- SAFETY: the last slot was written as @f tp@ for the @tp@ witnessing
  -- the @::> tp@ in the context; coercing back to that type is sound.
  let lastElem = unsafeFromAny (index# arr m)
  pure (frozen, lastElem)
{-# INLINE unextend #-}

------------------------------------------------------------------------
-- Combine

-- | \(O(n)\).  Combine two 'SmallArrayF's element-wise.  Allocates a
-- fresh array of the same size.
zipWithFC ::
  (forall tp. f tp -> g tp -> h tp) ->
  SmallArrayF f ctx ->
  SmallArrayF g ctx ->
  SmallArrayF h ctx
zipWithFC fn (SmallArrayF xs) (SmallArrayF ys) = runST $ do
  let n = size# xs
  mut <- newMut# n
  forN_ n $ \i ->
    writeMut# mut i (toAny (fn (index# xs i) (index# ys i)))
  freezeMut mut
{-# INLINE zipWithFC #-}

-- | \(O(n)\) plus the cost of the @m@-actions.  Combine two
-- 'SmallArrayF's element-wise under an effectful combinator.
zipWithMFC ::
  Applicative m =>
  (forall tp. f tp -> g tp -> m (h tp)) ->
  SmallArrayF f ctx ->
  SmallArrayF g ctx ->
  m (SmallArrayF h ctx)
zipWithMFC fn (SmallArrayF xs) (SmallArrayF ys) =
  unsafeFromListN# n <$> go 0#
  where
    n = size# xs
    go i
      | isTrue# (i >=# n) = pure []
      | otherwise =
          (:) <$> (toAny <$> fn (index# xs i) (index# ys i)) <*> go (i +# 1#)
{-# INLINE [1] zipWithMFC #-}
{-# RULES "zipWithMFC/ST"
    forall (fn :: forall tp. f tp -> g tp -> ST s (h tp)).
    zipWithMFC fn = zipWithMFCST fn #-}
{-# RULES "zipWithMFC/IO"
    forall (fn :: forall tp. f tp -> g tp -> IO (h tp)).
    zipWithMFC fn = zipWithMFCIO fn #-}

-- | Like 'zipWithMFC' specialized to 'ST'.  Writes results directly
-- into the output array with no intermediate list.
zipWithMFCST ::
  forall k (f :: k -> Type) (g :: k -> Type) (h :: k -> Type)
           (ctx :: Ctx k) s.
  (forall tp. f tp -> g tp -> ST s (h tp)) ->
  SmallArrayF f ctx ->
  SmallArrayF g ctx ->
  ST s (SmallArrayF h ctx)
zipWithMFCST fn (SmallArrayF xs) (SmallArrayF ys) = do
  let n = size# xs
  mut <- newMut# n
  -- SAFETY: same-ctx arrays share the same tp at each slot.
  forN_ n $ \i -> do
    z <- fn (index# xs i) (index# ys i)
    writeMut# mut i (toAny z)
  freezeMut mut
{-# INLINE zipWithMFCST #-}

-- | Like 'zipWithMFC' specialized to 'MonadIO'.  Writes results
-- directly into the output array with no intermediate list.
zipWithMFCIO ::
  forall k (f :: k -> Type) (g :: k -> Type) (h :: k -> Type)
           (ctx :: Ctx k) m.
  MonadIO m =>
  (forall tp. f tp -> g tp -> m (h tp)) ->
  SmallArrayF f ctx ->
  SmallArrayF g ctx ->
  m (SmallArrayF h ctx)
zipWithMFCIO fn (SmallArrayF xs) (SmallArrayF ys) = do
  let n = size# xs
  mut <- liftIO (stToIO (newMut# n))
  -- SAFETY: same-ctx arrays share the same tp at each slot.
  forN_ n $ \i -> do
    z <- fn (index# xs i) (index# ys i)
    liftIO (stToIO (writeMut# mut i (toAny z)))
  liftIO (stToIO (freezeMut mut))
{-# INLINE zipWithMFCIO #-}
{-# SPECIALIZE zipWithMFCIO ::
      (forall tp. f tp -> g tp -> IO (h tp))
   -> SmallArrayF f ctx
   -> SmallArrayF g ctx
   -> IO (SmallArrayF h ctx) #-}

-- | \(O(n)\).  Concatenate two 'SmallArrayF's.  Allocates a fresh
-- array of size @|ctx| + |ctx'|@.
append ::
  SmallArrayF f ctx ->
  SmallArrayF f ctx' ->
  SmallArrayF f (ctx <+> ctx')
append (SmallArrayF xs) (SmallArrayF ys) = runST $ do
  let nx = size# xs
      ny = size# ys
  mut <- newMut# (nx +# ny)
  copyIntoAt# xs 0# mut 0# nx
  copyIntoAt# ys 0# mut nx ny
  freezeMut mut
{-# INLINE [1] append #-}

------------------------------------------------------------------------
-- Subarray

-- | \(O(n)\).  Return the first @|ctx|@ elements of a concatenated
-- array, discarding the suffix.  Allocates a fresh array of size
-- @|ctx|@.
take ::
  Size ctx ->
  Size ctx' ->
  SmallArrayF f (ctx <+> ctx') ->
  SmallArrayF f ctx
take szCtx _ (SmallArrayF arr) = runST $ do
  let !(I# n) = Ctx.sizeInt szCtx
  mut <- newMut# n
  copyIntoAt# arr 0# mut 0# n
  freezeMut mut
{-# INLINE [1] take #-}
{-# RULES "take/append"
    forall (a :: SmallArrayF f ctx)
           (b :: SmallArrayF f ctx').
    take (size a) (size b) (append a b) = a #-}

-- | \(O(n)\).  Return the last @|ctx'|@ elements of a concatenated
-- array, discarding the prefix.  Allocates a fresh array of size
-- @|ctx'|@.
drop ::
  Size ctx ->
  Size ctx' ->
  SmallArrayF f (ctx <+> ctx') ->
  SmallArrayF f ctx'
drop szCtx szCtx' (SmallArrayF arr) = runST $ do
  let !(I# off) = Ctx.sizeInt szCtx
      !(I# n) = Ctx.sizeInt szCtx'
  mut <- newMut# n
  copyIntoAt# arr off mut 0# n
  freezeMut mut
{-# INLINE [1] drop #-}
{-# RULES "drop/append"
    forall (a :: SmallArrayF f ctx)
           (b :: SmallArrayF f ctx').
    drop (size a) (size b) (append a b) = b #-}

------------------------------------------------------------------------
-- Conversion to/from Assignment

-- | \(O(n)\).  Build a 'SmallArrayF' from an 'Assignment', copying
-- element pointers into a fresh small array.
fromAssignment :: Assignment f ctx -> SmallArrayF f ctx
fromAssignment a = runST $ do
  let !(I# n) = Ctx.sizeInt (Ctx.size a)
  mut <- newMut# n
  -- ifoldrFC visits each element once (O(n) total); indexVal gives the
  -- write position without a second tree lookup.
  ifoldrFC (\idx x rest ->
              let !(I# i#) = Ctx.indexVal idx
              in writeMut# mut i# (toAny x) >> rest)
           (pure ())
           a
  freezeMut mut
{-# INLINE [1] fromAssignment #-}
{-# RULES "fromAssignment/toAssignment"
    forall a. fromAssignment (toAssignment a) = a #-}

-- | \(O(n)\).  Build an 'Assignment' from a 'SmallArrayF'.
toAssignment :: SmallArrayF f ctx -> Assignment f ctx
toAssignment a = Ctx.generate (size a) (a !)
{-# INLINE [1] toAssignment #-}
{-# RULES "toAssignment/fromAssignment"
    forall a. toAssignment (fromAssignment a) = a #-}

------------------------------------------------------------------------
-- Instances

-- | Forces each element to WHNF (matching 'Data.Primitive.SmallArray.SmallArray').
-- Does not force the elements' contents.
instance NFData (SmallArrayF f ctx) where
  rnf (SmallArrayF arr) = foldlArr' (\() x -> x `seq` ()) () arr

-- Out-of-line worker for 'fmapFC'; named so that RULES can target it.
fmapFC_ ::
  (forall tp. f tp -> g tp) ->
  SmallArrayF f ctx ->
  SmallArrayF g ctx
fmapFC_ h (SmallArrayF arr) = runST $ do
  let n = size# arr
  mut <- newMut# n
  forN_ n $ \i ->
    writeMut# mut i (toAny (h (index# arr i)))
  freezeMut mut
{-# INLINE [1] fmapFC_ #-}
{-# RULES "fmapFC_/id"
    forall arr.
    fmapFC_ (\x -> x) arr = arr #-}
{-# RULES "fmapFC_/fmapFC_"
    forall (h :: forall tp. g tp -> k tp)
           (g :: forall tp. f tp -> g tp)
           arr.
    fmapFC_ h (fmapFC_ g arr) = fmapFC_ (h . g) arr #-}
{-# RULES "fmapFC_/imapFC_"
    forall (h :: forall tp. g tp -> k tp)
           (g :: forall tp. Index ctx tp -> f tp -> g tp)
           arr.
    fmapFC_ h (imapFC_ g arr) = imapFC_ (\idx -> h . g idx) arr #-}

instance FunctorFC SmallArrayF where
  -- GHC 9.0-9.2 reject the pointfree form due to higher-rank
  -- polymorphism issues; on later GHCs we keep it pointfree so RULES
  -- targeting 'fmapFC_' can match on the method's LHS.
#if __GLASGOW_HASKELL__ < 904
  fmapFC h arr = fmapFC_ h arr
#else
  fmapFC = fmapFC_
#endif
  {-# INLINE fmapFC #-}

instance FoldableFC SmallArrayF where
  foldrFC h z (SmallArrayF arr) = foldrArr h z arr
  {-# INLINE foldrFC #-}

  foldlFC' h z0 (SmallArrayF arr) = foldlArr' h z0 arr
  {-# INLINE foldlFC' #-}

-- Out-of-line worker for 'traverseFC'; named so that RULES can target it.
traverseFC__ ::
  Applicative m =>
  (forall tp. f tp -> m (g tp)) ->
  SmallArrayF f ctx ->
  m (SmallArrayF g ctx)
traverseFC__ h (SmallArrayF arr) =
  unsafeFromListN# (size# arr)
    <$> foldrArr (\x rest -> (:) <$> h x <*> rest) (pure []) arr
{-# INLINE [1] traverseFC__ #-}
{-# RULES "traverseFC/ST"
    forall (h :: forall tp. f tp -> ST s (g tp)).
    traverseFC__ h = traverseFCST h #-}
{-# RULES "traverseFC/IO"
    forall (h :: forall tp. f tp -> IO (g tp)).
    traverseFC__ h = traverseFCIO h #-}
{-# RULES "traverseFC/fmapFC_"
    forall (h :: forall tp. g tp -> m (k tp))
           (g :: forall tp. f tp -> g tp)
           arr.
    traverseFC__ h (fmapFC_ g arr) = traverseFC__ (h . g) arr #-}

instance TraversableFC SmallArrayF where
#if __GLASGOW_HASKELL__ < 904
  traverseFC h arr = traverseFC__ h arr
#else
  traverseFC = traverseFC__
#endif
  {-# INLINE traverseFC #-}

type instance IndexF   (SmallArrayF f ctx) = Index ctx
type instance IxValueF (SmallArrayF f ctx) = f

instance forall k (f :: k -> Type) ctx. IxedF k (SmallArrayF f ctx) where
  ixF :: Index ctx x -> Lens.Traversal' (SmallArrayF f ctx) (f x)
  ixF idx f = adjustM f idx

instance forall k (f :: k -> Type) ctx. IxedF' k (SmallArrayF f ctx) where
  ixF' :: Index ctx x -> Lens.Lens' (SmallArrayF f ctx) (f x)
  ixF' idx f = adjustM f idx

-- Out-of-line worker for 'imapFC'; named so that RULES can target it.
imapFC_ ::
  (forall tp. Index ctx tp -> f tp -> g tp) ->
  SmallArrayF f ctx ->
  SmallArrayF g ctx
imapFC_ h (SmallArrayF arr) = runST $ do
  let n = size# arr
  mut <- newMut# n
  -- SAFETY: slot @i@ was written as @f tp@ for the @tp@ witnessed by @idx@.
  forIndices_ n $ \idx ->
    let !(I# i#) = Ctx.indexVal idx
    in writeMut# mut i# (toAny (h idx (unsafeFromAny (index# arr i#))))
  freezeMut mut
{-# INLINE [1] imapFC_ #-}
{-# RULES "imapFC_/fmapFC_"
    forall (h :: forall tp. Index ctx tp -> g tp -> k tp)
           (g :: forall tp. f tp -> g tp)
           arr.
    imapFC_ h (fmapFC_ g arr) = imapFC_ (\idx -> h idx . g) arr #-}
{-# RULES "imapFC_/imapFC_"
    forall (h :: forall tp. Index ctx tp -> g tp -> k tp)
           (g :: forall tp. Index ctx tp -> f tp -> g tp)
           arr.
    imapFC_ h (imapFC_ g arr) = imapFC_ (\idx -> h idx . g idx) arr #-}

instance FunctorFCWithIndex SmallArrayF where
#if __GLASGOW_HASKELL__ < 904
  imapFC h arr = imapFC_ h arr
#else
  imapFC = imapFC_
#endif
  {-# INLINE imapFC #-}

instance FoldableFCWithIndex SmallArrayF where
  ifoldrFC h z (SmallArrayF arr) = foldrArrWithIndex h z arr
  {-# INLINE ifoldrFC #-}

-- Out-of-line worker for 'itraverseFC'; named so that RULES can target it.
itraverseFC__ ::
  Applicative m =>
  (forall tp. Index ctx tp -> f tp -> m (g tp)) ->
  SmallArrayF f ctx ->
  m (SmallArrayF g ctx)
itraverseFC__ h (SmallArrayF arr) =
  unsafeFromListN# (size# arr)
    <$> foldrArrWithIndex
          (\idx x rest -> (:) <$> (toAny <$> h idx x) <*> rest)
          (pure [])
          arr
{-# INLINE [1] itraverseFC__ #-}
{-# RULES "itraverseFC/ST"
    forall (h :: forall tp. Index ctx tp -> f tp -> ST s (g tp)).
    itraverseFC__ h = itraverseFCST h #-}
{-# RULES "itraverseFC/IO"
    forall (h :: forall tp. Index ctx tp -> f tp -> IO (g tp)).
    itraverseFC__ h = itraverseFCIO h #-}
{-# RULES "itraverseFC/fmapFC_"
    forall (h :: forall tp. Index ctx tp -> g tp -> m (k tp))
           (g :: forall tp. f tp -> g tp)
           arr.
    itraverseFC__ h (fmapFC_ g arr) = itraverseFC__ (\idx -> h idx . g) arr #-}
{-# RULES "itraverseFC/imapFC_"
    forall (h :: forall tp. Index ctx tp -> g tp -> m (k tp))
           (g :: forall tp. Index ctx tp -> f tp -> g tp)
           arr.
    itraverseFC__ h (imapFC_ g arr) = itraverseFC__ (\idx -> h idx . g idx) arr #-}

instance TraversableFCWithIndex SmallArrayF where
#if __GLASGOW_HASKELL__ < 904
  itraverseFC h arr = itraverseFC__ h arr
#else
  itraverseFC = itraverseFC__
#endif
  {-# INLINE itraverseFC #-}

------------------------------------------------------------------------
-- ST- and IO-specialised traversals

-- | Like 'traverseFC' specialised to 'ST'.  Writes each result
-- directly into the output array with no intermediate list.
traverseFCST ::
  forall k (f :: k -> Type) (g :: k -> Type) (ctx :: Ctx k) s.
  (forall tp. f tp -> ST s (g tp)) ->
  SmallArrayF f ctx ->
  ST s (SmallArrayF g ctx)
traverseFCST h (SmallArrayF arr) = do
  let n = size# arr
  mut <- newMut# n
  forN_ n $ \i -> do
    y <- h (index# arr i)
    writeMut# mut i (toAny y)
  freezeMut mut
{-# INLINE traverseFCST #-}

-- | Like 'traverseFC' specialised to 'MonadIO'.  Writes each result
-- directly into the output array with no intermediate list.
traverseFCIO ::
  forall k (f :: k -> Type) (g :: k -> Type) (ctx :: Ctx k) m.
  MonadIO m =>
  (forall tp. f tp -> m (g tp)) ->
  SmallArrayF f ctx ->
  m (SmallArrayF g ctx)
traverseFCIO h (SmallArrayF arr) = do
  let n = size# arr
  mut <- liftIO (stToIO (newMut# n))
  forN_ n $ \i -> do
    y <- h (index# arr i)
    liftIO (stToIO (writeMut# mut i (toAny y)))
  liftIO (stToIO (freezeMut mut))
{-# INLINE traverseFCIO #-}
{-# SPECIALIZE traverseFCIO ::
      (forall tp. f tp -> IO (g tp))
   -> SmallArrayF f ctx
   -> IO (SmallArrayF g ctx) #-}

-- | Like 'itraverseFC' specialised to 'ST'.  Writes each result
-- directly into the output array with no intermediate list.
itraverseFCST ::
  forall k (f :: k -> Type) (g :: k -> Type) (ctx :: Ctx k) s.
  (forall tp. Index ctx tp -> f tp -> ST s (g tp)) ->
  SmallArrayF f ctx ->
  ST s (SmallArrayF g ctx)
itraverseFCST h (SmallArrayF arr) = do
  let n = size# arr
  mut <- newMut# n
  -- SAFETY: slot i was written as f tp for the tp witnessed by idx.
  forIndices_ n $ \idx ->
    let !(I# i#) = Ctx.indexVal idx
    in do
      y <- h idx (unsafeFromAny (index# arr i#))
      writeMut# mut i# (toAny y)
  freezeMut mut
{-# INLINE itraverseFCST #-}

-- | Like 'itraverseFC' specialised to 'MonadIO'.  Writes each result
-- directly into the output array with no intermediate list.
itraverseFCIO ::
  forall k (f :: k -> Type) (g :: k -> Type) (ctx :: Ctx k) m.
  MonadIO m =>
  (forall tp. Index ctx tp -> f tp -> m (g tp)) ->
  SmallArrayF f ctx ->
  m (SmallArrayF g ctx)
itraverseFCIO h (SmallArrayF arr) = do
  let n = size# arr
  mut <- liftIO (stToIO (newMut# n))
  -- SAFETY: slot i was written as f tp for the tp witnessed by idx.
  forIndices_ n $ \idx ->
    let !(I# i#) = Ctx.indexVal idx
    in do
      y <- h idx (unsafeFromAny (index# arr i#))
      liftIO (stToIO (writeMut# mut i# (toAny y)))
  liftIO (stToIO (freezeMut mut))
{-# INLINE itraverseFCIO #-}
{-# SPECIALIZE itraverseFCIO ::
      (forall tp. Index ctx tp -> f tp -> IO (g tp))
   -> SmallArrayF f ctx
   -> IO (SmallArrayF g ctx) #-}

instance TestEqualityFC SmallArrayF where
  testEqualityFC eqElt (SmallArrayF x) (SmallArrayF y)
    | isTrue# (nx /=# ny) = Nothing
    | otherwise = go 0#
    where
      nx = size# x
      ny = size# y
      go i
        -- SAFETY: both arrays have the same length and all pairs of elements
        -- have been shown equal, so their contexts must agree.
        | isTrue# (i >=# nx) = Just unsafeAxiom
        | otherwise =
            case eqElt (index# x i) (index# y i) of
              Just _ -> go (i +# 1#)
              Nothing -> Nothing

instance OrdFC SmallArrayF where
  compareFC cmpElt (SmallArrayF x) (SmallArrayF y) =
    case compare (I# (size# x)) (I# (size# y)) of
      LT -> LTF
      GT -> GTF
      EQ -> go 0#
    where
      n = size# x
      go i
        -- SAFETY: sizes match and all pairs compare 'EQF', so the contexts
        -- agree; 'EQF' requires that witness.
        | isTrue# (i >=# n) = unsafeCoerce EQF
        | otherwise =
            case cmpElt (index# x i) (index# y i) of
              LTF -> LTF
              GTF -> GTF
              EQF -> go (i +# 1#)

instance TestEquality f => TestEquality (SmallArrayF f) where
  testEquality = testEqualityFC testEquality

instance TestEquality f => Eq (SmallArrayF f ctx) where
  x == y = isJust (testEquality x y)

instance OrdF f => OrdF (SmallArrayF f) where
  compareF = compareFC compareF

instance OrdF f => Ord (SmallArrayF f ctx) where
  compare x y = toOrdering (compareF x y)

instance ShowF f => Show (SmallArrayF f ctx) where
  show a =
    let xs = foldrFC (\e r -> showF e : r) [] a
    in "[" ++ intercalate ", " xs ++ "]"

instance ShowF f => ShowF (SmallArrayF f)

instance (HashableF f, TestEquality f) => Hashable (SmallArrayF f ctx) where
  hashWithSalt s a = foldlFC' hashWithSaltF s a

instance (HashableF f, TestEquality f) => HashableF (SmallArrayF f) where
  hashWithSaltF = hashWithSalt

