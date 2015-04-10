------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.UnsafeContext
-- Description      : Finite dependent products
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines type contexts as a data-kind that consists of
-- a list of types.  Indexes are defined on contexts in a way that
-- respects the type context: index 0 carries a type parameter that is
-- equal to the 0th element of its associated type context, etc.
--
-- In addition, finite dependent products (Assignements) are defined over
-- type contexts.  The elements of an assignment can be accessed using
-- appropriately-typed indices.
--
-- For performance reasons, unsafeCoerce is used to fib about the typing.
-- Thus, contexts are actually just vectors, and indices actually just
-- Ints.  We rely on the external type system to keep things straight.
-- See "SafeTypeContext" for a parallel implementation of this module
-- that uses only safe operations.
--
-- This unsafe implementation has the advantage that indices can be
-- cast into extended contexts just using DataCoerce.coerce, because Index
-- is just a newtype over Int, and because we count from the beginning of
-- the context (rather than the end, as in the safe implementation).
-- This turns out to be critical for good performance, as otherwise we must
-- repeatedly rebuild large datastructures just to extend embedded
-- context indices.
------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.UnsafeContext
  ( module Data.Parameterized.Ctx
  , KnownContext(..)
    -- * Size
  , Size
  , sizeInt
  , zeroSize
  , incSize
  , extSize
    -- * Diff
  , Diff
  , noDiff

  , extendRight
  , KnownDiff(..)
    -- * Indexing
  , Index
  , indexVal
  , base
  , skip

  , nextIndex
  , extendIndex
  , extendIndex'
  , forIndex
  , SomeIndex(..)
  , intIndex
    -- * Assignments
  , Assignment
  , size
  , generate
  , generateM
  , empty
  , extend
  , update
  , adjust
  , init
  , (!)
  , (!!)
  , toList
  , foldlF
  , foldrF
  , traverseF
  , map
  , zipWithM
  , (%>)
  ) where

import qualified Control.Category as Cat
import Control.DeepSeq
import qualified Control.Lens as Lens
import Control.Monad (liftM)
import qualified Control.Monad as Monad
import qualified Data.Foldable as Fold
import Data.List (intercalate)
import Data.Type.Equality
import qualified Data.Sequence as Seq
import GHC.Prim (Any)
import Prelude hiding (init, map, succ, (!!))
import Unsafe.Coerce

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative ((<$>), Applicative(..))
import Data.Traversable (traverse)
#endif

import Data.Parameterized.Classes
import Data.Parameterized.Ctx
import Data.Parameterized.TraversableFC

------------------------------------------------------------------------
-- Size

-- | Represents the size of a context.
newtype Size (ctx :: Ctx k) = Size { sizeInt :: Int }

-- | The size of an empty context.
zeroSize :: Size 'EmptyCtx
zeroSize = Size 0

-- | Increment the size to the next value.
incSize :: Size ctx -> Size (ctx '::> tp)
incSize (Size n) = Size (n+1)

------------------------------------------------------------------------
-- Size

-- | A context that can be determined statically at compiler time.
class KnownContext (ctx :: Ctx k) where
  knownSize :: Size ctx

instance KnownContext 'EmptyCtx where
  knownSize = zeroSize

instance KnownContext ctx => KnownContext (ctx '::> tp) where
  knownSize = incSize knownSize

------------------------------------------------------------------------
-- Diff

-- | Difference in number of elements between two contexts.
-- The first context must be a sub-context of the other.
newtype Diff (l :: Ctx k) (r :: Ctx k)
      = Diff { _contextExtSize :: Int }

-- | The identity difference.
noDiff :: Diff l l
noDiff = Diff 0

-- | Extend the difference to a sub-context of the right side.
extendRight :: Diff l r -> Diff l (r '::> tp)
extendRight (Diff i) = Diff (i+1)

instance Cat.Category Diff where
  id = Diff 0
  Diff j . Diff i = Diff (i + j)

-- | Extend the size by a given difference.
extSize :: Size l -> Diff l r -> Size r
extSize (Size i) (Diff j) = Size (i+j)

------------------------------------------------------------------------
-- KnownDiff

-- | A difference that can be automatically inferred at compile time.
class KnownDiff (l :: Ctx k) (r :: Ctx k) where
  knownDiff :: Diff l r

instance KnownDiff l l where
  knownDiff = noDiff

instance KnownDiff l r => KnownDiff l (r '::> tp) where
  knownDiff = extendRight knownDiff

------------------------------------------------------------------------
-- Index

-- | An index is a reference to a position with a particular type in a
-- context.
newtype Index (ctx :: Ctx k) (tp :: k) = Index { indexVal :: Int }

instance Eq (Index ctx tp) where
  Index i == Index j = i == j

instance TestEquality (Index ctx) where
  testEquality (Index i) (Index j)
    | i == j = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance Ord (Index ctx tp) where
  Index i `compare` Index j = compare i j

instance OrdF (Index ctx) where
  compareF (Index i) (Index j)
    | i < j = LTF
    | i == j = unsafeCoerce EQF
    | otherwise = GTF

-- | Index for first element in context.
base :: Index ('EmptyCtx '::> tp) tp
base = Index 0

-- | Increase context while staying at same index.
skip :: Index ctx x -> Index (ctx '::> y) x
skip (Index i) = Index i

-- | Return the index of a element one past the size.
nextIndex :: Size ctx -> Index (ctx '::> tp) tp
nextIndex (Size n) = Index n

{-# INLINE extendIndex #-}
extendIndex :: KnownDiff l r => Index l tp -> Index r tp
extendIndex = extendIndex' knownDiff

{-# INLINE extendIndex' #-}
extendIndex' :: Diff l r -> Index l tp -> Index r tp
extendIndex' _ = unsafeCoerce

-- | Given a size @n@, an initial value @v0@, and a function @f@, @forIndex n v0 f@,
-- calls @f@ on each index less than @n@ starting from @0@ and @v0@, with the value @v@ obtained
-- from the last call.
forIndex :: forall ctx r
          . Size ctx
         -> (forall tp . r -> Index ctx tp -> r)
         -> r
         -> r
forIndex (Size n) f = go 0
  where go :: Int -> r -> r
        go i v | i < n = go (i+1) (f v (Index i))
               | otherwise = v

data SomeIndex ctx where
  SomeIndex :: Index ctx tp -> SomeIndex ctx

-- | Return index at given integer or nothing if integer is out of bounds.
intIndex :: Int -> Size ctx -> Maybe (SomeIndex ctx)
intIndex i (Size n) | 0 <= i && i < n = Just (SomeIndex (Index i))
                           | otherwise = Nothing

instance Show (Index ctx tp) where
   show = show . indexVal

instance ShowF (Index ctx) where
   showF = show

------------------------------------------------------------------------
-- Assignment

newtype Assignment (f :: k -> *) (c :: Ctx k) = Assignment (Seq.Seq Any)

instance NFData (Assignment f ctx) where
  rnf (Assignment v) = seq (Fold.all (\e -> e `seq` True) v) ()

size :: Assignment f ctx -> Size ctx
size (Assignment v) = Size (Seq.length v)

unsafeCoerceToAny :: f tp -> Any
unsafeCoerceToAny = unsafeCoerce

unsafeCoerceFromAny :: Any -> f tp
unsafeCoerceFromAny = unsafeCoerce

-- | Generate an assignment
generate :: Size ctx
         -> (forall tp . Index ctx tp -> f tp)
         -> Assignment f ctx
generate (Size n) f = force $ Assignment $ go 0 Seq.empty
  where go i s | i == n = s
        go i s = go (i+1) (s Seq.|> unsafeCoerceToAny (f (Index i)))

{-# NOINLINE generateM #-}
-- | Generate an assignment
generateM :: Monad m
          => Size ctx
          -> (forall tp . Index ctx tp -> m (f tp))
          -> m (Assignment f ctx)
generateM (Size n) f = (force . Assignment) `liftM` go 0 Seq.empty
  where go i s | i == n = return s
        go i s = do
          r <- f (Index i)
          go (i+1) ((Seq.|>) s $! unsafeCoerceToAny r)

-- | Create empty indexec vector.
empty :: Assignment f 'EmptyCtx
empty = Assignment Seq.empty

extend :: Assignment f ctx -> f tp -> Assignment f (ctx '::> tp)
extend (Assignment v) e = seq e $ Assignment (v Seq.|> unsafeCoerceToAny e)

-- This is an unsafe version of update that changes the type of the expression.
unsafeUpdate :: Int -> Assignment f ctx -> f u -> Assignment f ctx'
unsafeUpdate idx (Assignment v) e = Assignment (Seq.update idx (unsafeCoerceToAny e) v)

update :: Index ctx tp -> f tp -> Assignment f ctx -> Assignment f ctx
update (Index idx) e a = unsafeUpdate idx a e

adjust :: (f tp -> f tp) -> Index ctx tp -> Assignment f ctx -> Assignment f ctx
adjust f (Index idx) (Assignment v) =
  Assignment (Seq.adjust (unsafeCoerceToAny . f . unsafeCoerceFromAny) idx v)

-- | Return assignment with all but the last block.
init :: Assignment f (ctx '::> tp) -> Assignment f ctx
init (Assignment v) =
  case Seq.viewr v of
    u Seq.:> _ -> Assignment u
    _ -> error "internal: init given bad value"

-- Unexported index that returns an arbitrary type of expression.
unsafeIndex :: Int -> Assignment f ctx -> f u
unsafeIndex idx (Assignment v) = unsafeCoerceFromAny (v `Seq.index` idx)

-- | Return value of assignment.
(!) :: Assignment f ctx -> Index ctx tp -> f tp
a ! Index i = unsafeIndex i a

-- | Return value of assignment.
(!!) :: KnownDiff l r => Assignment f r -> Index l tp -> f tp
a !! i = a ! extendIndex i

assignmentEq :: (forall u v . f u -> f v -> Maybe (u :~: v))
             -> Assignment f c -> Assignment f d -> Maybe (c :~: d)
assignmentEq eqC (Assignment xv) (Assignment yv) = do
  let go (xh:xr) (yh:yr)
        | Just _ <- eqC (unsafeCoerceFromAny xh) (unsafeCoerceFromAny yh)
        = go xr yr
      go [] [] = Just (unsafeCoerce Refl)
      go _ _ = Nothing
  go (Fold.toList xv) (Fold.toList yv)

instance TestEquality f => TestEquality (Assignment f) where
  testEquality = assignmentEq testEquality

instance TestEquality f => Eq (Assignment f ctx) where
  x == y = isJust (testEquality x y)

instance TestEquality f => PolyEq (Assignment f x) (Assignment f y) where
  polyEqF x y = fmap (\Refl -> Refl) $ testEquality x y

instance ShowF f => ShowF (Assignment f) where
  showF a = "[" ++ intercalate ", " (toList showF a) ++ "]"

instance ShowF f => Show (Assignment f ctx) where
  show a = showF a

instance FunctorFC Assignment where
  fmapFC = fmapFCDefault

instance FoldableFC Assignment where
  foldMapFC = foldMapFCDefault

instance TraversableFC Assignment where
  traverseFC f (Assignment v) =
    force . Assignment <$> traverse (\a -> unsafeCoerceToAny <$> f (unsafeCoerceFromAny a)) v

-- | Map assignment
map :: (forall tp . f tp -> g tp) -> Assignment f c -> Assignment g c
map = fmapFC

-- | A left fold over an assignment.
foldlF :: (forall tp . r -> f tp -> r)
       -> r
       -> Assignment f c
       -> r
foldlF = foldlFC

-- | A right fold over an assignment.
foldrF :: (forall tp . f tp -> r -> r)
       -> r
       -> Assignment f c
       -> r
foldrF = foldrFC

traverseF :: Applicative m
          => (forall tp . f tp -> m (g tp))
          -> Assignment f c
          -> m (Assignment g c)
traverseF = traverseFC

-- | Convert assignment to list.
toList :: (forall tp . f tp -> a)
       -> Assignment f c
       -> [a]
toList = toListFC

zipWithM :: Monad m
         => (forall tp . f tp -> g tp -> m (h tp))
         -> Assignment f c
         -> Assignment g c
         -> m (Assignment h c)
zipWithM f (Assignment u0) (Assignment v0) = do
  let go a b = unsafeCoerceToAny `liftM` f (unsafeCoerceFromAny a) (unsafeCoerceFromAny b)
  r <- (Assignment . Seq.fromList) `liftM` Monad.zipWithM go (Fold.toList u0) (Fold.toList v0)
  deepseq r $ return r

(%>) :: Assignment f x -> f tp -> Assignment f (x '::> tp)
a %> v = extend a v

------------------------------------------------------------------------
-- Lens combinators

unsafeLens :: Int -> Lens.Lens (Assignment f ctx) (Assignment f ctx') (f tp) (f u)
unsafeLens idx = Lens.lens (unsafeIndex idx) (unsafeUpdate idx)

------------------------------------------------------------------------
-- 1 field lens combinators

type Assignment1 f x1 = Assignment f ('EmptyCtx '::> x1)

instance Lens.Field1 (Assignment1 f t) (Assignment1 f u) (f t) (f u) where
  _1 = unsafeLens 0

------------------------------------------------------------------------
-- 2 field lens combinators

type Assignment2 f x1 x2
   = Assignment f ('EmptyCtx '::> x1 '::> x2)

instance Lens.Field1 (Assignment2 f t x2) (Assignment2 f u x2) (f t) (f u) where
  _1 = unsafeLens 0

instance Lens.Field2 (Assignment2 f x1 t) (Assignment2 f x1 u) (f t) (f u) where
  _2 = unsafeLens 1

------------------------------------------------------------------------
-- 3 field lens combinators

type Assignment3 f x1 x2 x3
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3)

instance Lens.Field1 (Assignment3 f t x2 x3)
                     (Assignment3 f u x2 x3)
                     (f t)
                     (f u) where
  _1 = unsafeLens 0


instance Lens.Field2 (Assignment3 f x1 t x3)
                     (Assignment3 f x1 u x3)
                     (f t)
                     (f u) where
  _2 = unsafeLens 1

instance Lens.Field3 (Assignment3 f x1 x2 t)
                     (Assignment3 f x1 x2 u)
                     (f t)
                     (f u) where
  _3 = unsafeLens 2

------------------------------------------------------------------------
-- 4 field lens combinators

type Assignment4 f x1 x2 x3 x4
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4)

instance Lens.Field1 (Assignment4 f t x2 x3 x4)
                     (Assignment4 f u x2 x3 x4)
                     (f t)
                     (f u) where
  _1 = unsafeLens 0


instance Lens.Field2 (Assignment4 f x1 t x3 x4)
                     (Assignment4 f x1 u x3 x4)
                     (f t)
                     (f u) where
  _2 = unsafeLens 1

instance Lens.Field3 (Assignment4 f x1 x2 t x4)
                     (Assignment4 f x1 x2 u x4)
                     (f t)
                     (f u) where
  _3 = unsafeLens 2

instance Lens.Field4 (Assignment4 f x1 x2 x3 t)
                     (Assignment4 f x1 x2 x3 u)
                     (f t)
                     (f u) where
  _4 = unsafeLens 3

------------------------------------------------------------------------
-- 5 field lens combinators

type Assignment5 f x1 x2 x3 x4 x5
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5)

instance Lens.Field1 (Assignment5 f t x2 x3 x4 x5)
                     (Assignment5 f u x2 x3 x4 x5)
                     (f t)
                     (f u) where
  _1 = unsafeLens 0

instance Lens.Field2 (Assignment5 f x1 t x3 x4 x5)
                     (Assignment5 f x1 u x3 x4 x5)
                     (f t)
                     (f u) where
  _2 = unsafeLens 1

instance Lens.Field3 (Assignment5 f x1 x2 t x4 x5)
                     (Assignment5 f x1 x2 u x4 x5)
                     (f t)
                     (f u) where
  _3 = unsafeLens 2

instance Lens.Field4 (Assignment5 f x1 x2 x3 t x5)
                     (Assignment5 f x1 x2 x3 u x5)
                     (f t)
                     (f u) where
  _4 = unsafeLens 3

instance Lens.Field5 (Assignment5 f x1 x2 x3 x4 t)
                     (Assignment5 f x1 x2 x3 x4 u)
                     (f t)
                     (f u) where
  _5 = unsafeLens 4

------------------------------------------------------------------------
-- 6 field lens combinators

type Assignment6 f x1 x2 x3 x4 x5 x6
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6)

instance Lens.Field1 (Assignment6 f t x2 x3 x4 x5 x6)
                     (Assignment6 f u x2 x3 x4 x5 x6)
                     (f t)
                     (f u) where
  _1 = unsafeLens 0


instance Lens.Field2 (Assignment6 f x1 t x3 x4 x5 x6)
                     (Assignment6 f x1 u x3 x4 x5 x6)
                     (f t)
                     (f u) where
  _2 = unsafeLens 1

instance Lens.Field3 (Assignment6 f x1 x2 t x4 x5 x6)
                     (Assignment6 f x1 x2 u x4 x5 x6)
                     (f t)
                     (f u) where
  _3 = unsafeLens 2

instance Lens.Field4 (Assignment6 f x1 x2 x3 t x5 x6)
                     (Assignment6 f x1 x2 x3 u x5 x6)
                     (f t)
                     (f u) where
  _4 = unsafeLens 3

instance Lens.Field5 (Assignment6 f x1 x2 x3 x4 t x6)
                     (Assignment6 f x1 x2 x3 x4 u x6)
                     (f t)
                     (f u) where
  _5 = unsafeLens 4

instance Lens.Field6 (Assignment6 f x1 x2 x3 x4 x5 t)
                     (Assignment6 f x1 x2 x3 x4 x5 u)
                     (f t)
                     (f u) where
  _6 = unsafeLens 5

------------------------------------------------------------------------
-- 7 field lens combinators

type Assignment7 f x1 x2 x3 x4 x5 x6 x7
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6 '::> x7)

instance Lens.Field1 (Assignment7 f t x2 x3 x4 x5 x6 x7)
                     (Assignment7 f u x2 x3 x4 x5 x6 x7)
                     (f t)
                     (f u) where
  _1 = unsafeLens 0


instance Lens.Field2 (Assignment7 f x1 t x3 x4 x5 x6 x7)
                     (Assignment7 f x1 u x3 x4 x5 x6 x7)
                     (f t)
                     (f u) where
  _2 = unsafeLens 1

instance Lens.Field3 (Assignment7 f x1 x2 t x4 x5 x6 x7)
                     (Assignment7 f x1 x2 u x4 x5 x6 x7)
                     (f t)
                     (f u) where
  _3 = unsafeLens 2

instance Lens.Field4 (Assignment7 f x1 x2 x3 t x5 x6 x7)
                     (Assignment7 f x1 x2 x3 u x5 x6 x7)
                     (f t)
                     (f u) where
  _4 = unsafeLens 3

instance Lens.Field5 (Assignment7 f x1 x2 x3 x4 t x6 x7)
                     (Assignment7 f x1 x2 x3 x4 u x6 x7)
                     (f t)
                     (f u) where
  _5 = unsafeLens 4

instance Lens.Field6 (Assignment7 f x1 x2 x3 x4 x5 t x7)
                     (Assignment7 f x1 x2 x3 x4 x5 u x7)
                     (f t)
                     (f u) where
  _6 = unsafeLens 5

instance Lens.Field7 (Assignment7 f x1 x2 x3 x4 x5 x6 t)
                     (Assignment7 f x1 x2 x3 x4 x5 x6 u)
                     (f t)
                     (f u) where
  _7 = unsafeLens 6

------------------------------------------------------------------------
-- 8 field lens combinators

type Assignment8 f x1 x2 x3 x4 x5 x6 x7 x8
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6 '::> x7 '::> x8)

instance Lens.Field1 (Assignment8 f t x2 x3 x4 x5 x6 x7 x8)
                     (Assignment8 f u x2 x3 x4 x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _1 = unsafeLens 0


instance Lens.Field2 (Assignment8 f x1 t x3 x4 x5 x6 x7 x8)
                     (Assignment8 f x1 u x3 x4 x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _2 = unsafeLens 1

instance Lens.Field3 (Assignment8 f x1 x2 t x4 x5 x6 x7 x8)
                     (Assignment8 f x1 x2 u x4 x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _3 = unsafeLens 2

instance Lens.Field4 (Assignment8 f x1 x2 x3 t x5 x6 x7 x8)
                     (Assignment8 f x1 x2 x3 u x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _4 = unsafeLens 3

instance Lens.Field5 (Assignment8 f x1 x2 x3 x4 t x6 x7 x8)
                     (Assignment8 f x1 x2 x3 x4 u x6 x7 x8)
                     (f t)
                     (f u) where
  _5 = unsafeLens 4

instance Lens.Field6 (Assignment8 f x1 x2 x3 x4 x5 t x7 x8)
                     (Assignment8 f x1 x2 x3 x4 x5 u x7 x8)
                     (f t)
                     (f u) where
  _6 = unsafeLens 5

instance Lens.Field7 (Assignment8 f x1 x2 x3 x4 x5 x6 t x8)
                     (Assignment8 f x1 x2 x3 x4 x5 x6 u x8)
                     (f t)
                     (f u) where
  _7 = unsafeLens 6

instance Lens.Field8 (Assignment8 f x1 x2 x3 x4 x5 x6 x7 t)
                     (Assignment8 f x1 x2 x3 x4 x5 x6 x7 u)
                     (f t)
                     (f u) where
  _8 = unsafeLens 7

------------------------------------------------------------------------
-- 9 field lens combinators

type Assignment9 f x1 x2 x3 x4 x5 x6 x7 x8 x9
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6 '::> x7 '::> x8 '::> x9)


instance Lens.Field1 (Assignment9 f t x2 x3 x4 x5 x6 x7 x8 x9)
                     (Assignment9 f u x2 x3 x4 x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _1 = unsafeLens 0

instance Lens.Field2 (Assignment9 f x1 t x3 x4 x5 x6 x7 x8 x9)
                     (Assignment9 f x1 u x3 x4 x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _2 = unsafeLens 1

instance Lens.Field3 (Assignment9 f x1 x2 t x4 x5 x6 x7 x8 x9)
                     (Assignment9 f x1 x2 u x4 x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _3 = unsafeLens 2

instance Lens.Field4 (Assignment9 f x1 x2 x3 t x5 x6 x7 x8 x9)
                     (Assignment9 f x1 x2 x3 u x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _4 = unsafeLens 3

instance Lens.Field5 (Assignment9 f x1 x2 x3 x4 t x6 x7 x8 x9)
                     (Assignment9 f x1 x2 x3 x4 u x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _5 = unsafeLens 4

instance Lens.Field6 (Assignment9 f x1 x2 x3 x4 x5 t x7 x8 x9)
                     (Assignment9 f x1 x2 x3 x4 x5 u x7 x8 x9)
                     (f t)
                     (f u) where
  _6 = unsafeLens 5

instance Lens.Field7 (Assignment9 f x1 x2 x3 x4 x5 x6 t x8 x9)
                     (Assignment9 f x1 x2 x3 x4 x5 x6 u x8 x9)
                     (f t)
                     (f u) where
  _7 = unsafeLens 6

instance Lens.Field8 (Assignment9 f x1 x2 x3 x4 x5 x6 x7 t x9)
                     (Assignment9 f x1 x2 x3 x4 x5 x6 x7 u x9)
                     (f t)
                     (f u) where
  _8 = unsafeLens 7

instance Lens.Field9 (Assignment9 f x1 x2 x3 x4 x5 x6 x7 x8 t)
                     (Assignment9 f x1 x2 x3 x4 x5 x6 x7 x8 u)
                     (f t)
                     (f u) where
  _9 = unsafeLens 8