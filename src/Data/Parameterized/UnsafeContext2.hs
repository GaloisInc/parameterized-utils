------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.UnsafeContext2
-- Description      : Finite dependent products
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
--------------------------------------------------------------------------
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.UnsafeContext2
  ( module Data.Parameterized.Ctx
  , Size
  , sizeInt
  , zeroSize
  , incSize
  , extSize
  , KnownContext(..)
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
  , intIndex
    -- * Assignments
  , Assignment
  , size
  , replicate
  , generate
  , generateM
  , empty
  , null
  , extend
  , update
  , adjust
  , init
  , AssignView(..)
  , view
  , (!)
  , (!!)
  , toList
  , zipWith
  , zipWithM
  , (%>)
  , traverseWithIndex
  ) where

import qualified Control.Category as Cat
import Control.DeepSeq
import qualified Control.Lens as Lens
import Control.Monad.Identity (Identity(..))
import Data.Hashable
import Data.List (intercalate)
import Data.Type.Equality
import Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import Prelude hiding (init, map, null, replicate, succ, zipWith, (!!))

import Unsafe.Coerce
import GHC.Exts (Any)

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
import Control.Applicative (Applicative(..))
#endif

import Data.Parameterized.Classes
import Data.Parameterized.Ctx
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC

{-# NOINLINE toAny #-}
toAny :: forall (f::k -> *) (tp::k) . f tp -> Any
toAny = unsafeCoerce

{-# NOINLINE fromAny #-}
fromAny :: forall (f::k -> *) (tp::k). Any -> f tp
fromAny = unsafeCoerce

------------------------------------------------------------------------
-- Size

-- | Represents the size of a context.
newtype Size (ctx :: Ctx k) = Size { sizeInt :: Int }

-- | The size of an empty context.
zeroSize :: Size 'EmptyCtx
zeroSize = Size 0

-- | Increment the size to the next value.
incSize :: Size ctx -> Size (ctx '::> tp)
incSize (Size n) = (Size (n+1))

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
newtype Diff (l :: Ctx k) (r :: Ctx k) = Diff Int

-- | The identity difference.
noDiff :: Diff l l
noDiff = Diff 0

-- | Extend the difference to a sub-context of the right side.
extendRight :: Diff l r -> Diff l (r '::> tp)
extendRight (Diff diff) = (Diff (diff+1))

composeDiff :: Diff a b -> Diff b c -> Diff a c
composeDiff (Diff x) (Diff y) = Diff (x+y)

instance Cat.Category Diff where
  id = noDiff
  d1 . d2 = composeDiff d2 d1

-- | Extend the size by a given difference.
extSize :: Size l -> Diff l r -> Size r
extSize (Size n) (Diff d) = Size (n+d)

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
newtype Index (ctx :: Ctx k) (tp :: k)
  = Index { indexVal :: Int }

instance Eq (Index ctx tp) where
  idx1 == idx2 = isJust (testEquality idx1 idx2)

instance TestEquality (Index ctx) where
  {-# NOINLINE testEquality #-}
  testEquality (Index x) (Index y)
     | x == y    = unsafeCoerce (Just Refl)
     | otherwise = Nothing

instance Ord (Index ctx tp) where
  compare i j = toOrdering (compareF i j)

instance OrdF (Index ctx) where
  {-# NOINLINE compareF #-}
  compareF (Index x) (Index y)
    | x <  y   = LTF
    | x == y   = unsafeCoerce EQF
    | otherwise = GTF

-- | Index for first element in context.
base :: Index ('EmptyCtx '::> tp) tp
base = Index 0

-- | Increase context while staying at same index.
skip :: Index ctx x -> Index (ctx '::> y) x
skip (Index idx) = (Index idx)

 -- | Return the index of a element one past the size.
nextIndex :: Size ctx -> Index (ctx '::> tp) tp
nextIndex (Size sz) = Index sz

{-# INLINE extendIndex #-}
extendIndex :: KnownDiff l r => Index l tp -> Index r tp
extendIndex = extendIndex' knownDiff

{-# INLINE extendIndex' #-}
extendIndex' :: Diff l r -> Index l tp -> Index r tp
extendIndex' _ (Index idx) = (Index idx)

-- | Given a size @n@, an initial value @v0@, and a function @f@, @forIndex n v0 f@,
-- calls @f@ on each index less than @n@ starting from @0@ and @v0@, with the value @v@ obtained
-- from the last call.
forIndex :: forall ctx r
          . Size ctx
         -> (forall tp . r -> Index ctx tp -> r)
         -> r
         -> r
forIndex (Size sz) f z = foldl (\r i -> f r (Index i)) z [ 0 .. (sz-1) ]

-- | Return index at given integer or nothing if integer is out of bounds.
intIndex :: Int -> Size ctx -> Maybe (Some (Index ctx))
intIndex n (Size sz)
   | n < sz    = Just (Some (Index n))
   | otherwise = Nothing

instance Show (Index ctx tp) where
   show = show . indexVal

instance ShowF (Index ctx) where
   showF = show

------------------------------------------------------------------------
-- Assignment

newtype Assignment (f::k -> *) (ctx :: Ctx k) = Assignment (Seq Any)

data AssignView f ctx where
  AssignEmpty :: AssignView f EmptyCtx
  AssignExtend :: Assignment f ctx
               -> f tp
               -> AssignView f (ctx::>tp)

{-# NOINLINE view #-}
view :: forall f ctx . Assignment f ctx -> AssignView f ctx
view (Assignment s)
  | Seq.null   s = unsafeCoerce AssignEmpty
  | otherwise    = unsafeCoerce
       (AssignExtend
           (Assignment (Seq.take (Seq.length s - 1) s))
           (fromAny (Seq.index s (Seq.length s - 1))))

instance NFData (Assignment f ctx) where
  rnf (Assignment s) = s `seq` ()

size :: Assignment f ctx -> Size ctx
size (Assignment s) = Size (Seq.length s)

-- | Generate an assignment
generate :: forall ctx f
          . Size ctx
         -> (forall tp . Index ctx tp -> f tp)
         -> Assignment f ctx
generate (Size sz) f =
  Assignment $ Seq.fromFunction sz $ \i -> toAny (f (Index i))

-- | Generate an assignment
generateM :: forall ctx m f
           . Applicative m
          => Size ctx
          -> (forall tp . Index ctx tp -> m (f tp))
          -> m (Assignment f ctx)
generateM (Size sz) f =
  Assignment <$> traverse (\i -> toAny <$> f (Index i)) (Seq.fromFunction sz id)

-- | @replicate n@ make a context with different copies of the same
-- polymorphic value.
replicate :: Size ctx -> (forall tp . f tp) -> Assignment f ctx
replicate n c = generate n (\_ -> c)

-- | Create empty indexec vector.
empty :: Assignment f 'EmptyCtx
empty = Assignment Seq.empty

-- | Return true if assignment is empty.
null :: Assignment f ctx -> Bool
null (Assignment s) = Seq.null s

extend :: Assignment f ctx -> f tp -> Assignment f (ctx '::> tp)
extend (Assignment asgn) e = Assignment (asgn Seq.|> (toAny e))

update :: Index ctx tp -> f tp -> Assignment f ctx -> Assignment f ctx
update idx e asgn = adjust (\_ -> e) idx asgn

adjust :: forall f ctx tp. (f tp -> f tp) -> Index ctx tp -> Assignment f ctx -> Assignment f ctx
adjust f (Index idx) (Assignment a) = Assignment $ Seq.adjust (toAny . f . fromAny) idx a 

-- | Return assignment with all but the last block.
init :: Assignment f (ctx '::> tp) -> Assignment f ctx
init (Assignment asgn) = Assignment (Seq.take (Seq.length asgn - 1) asgn)

-- | Return value of assignment.
(!) :: Assignment f ctx -> Index ctx tp -> f tp
(!) (Assignment asgn) (Index idx) = fromAny (Seq.index asgn idx)

-- | Return value of assignment.
(!!) :: KnownDiff l r => Assignment f r -> Index l tp -> f tp
a !! i = a ! extendIndex i

instance TestEquality f => Eq (Assignment f ctx) where
  x == y = isJust (testEquality x y)

testEq :: TestEquality f => AssignView f cxt1 -> AssignView f cxt2 -> Maybe (cxt1 :~: cxt2)
testEq AssignEmpty AssignEmpty = Just Refl
testEq (AssignExtend ctx1 x1) (AssignExtend ctx2 x2) =
     case testEq (view ctx1) (view ctx2) of
       Nothing -> Nothing
       Just Refl ->
          case testEquality x1 x2 of
             Nothing -> Nothing
             Just Refl -> Just Refl
testEq _ _ = error "Data.Parameterized.SafeContext.testEquality: impossible!"


instance TestEquality f => TestEquality (Assignment f) where
   testEquality x y = testEq (view x) (view y)

instance TestEquality f => PolyEq (Assignment f x) (Assignment f y) where
  polyEqF x y = fmap (\Refl -> Refl) $ testEquality x y

compareAsgn :: OrdF f => AssignView f ctx1 -> AssignView f ctx2 -> OrderingF ctx1 ctx2
compareAsgn AssignEmpty AssignEmpty = EQF
compareAsgn AssignEmpty _ = GTF
compareAsgn _ AssignEmpty = LTF
compareAsgn (AssignExtend ctx1 x) (AssignExtend ctx2 y) =
  case compareAsgn (view ctx1) (view ctx2) of
    LTF -> LTF
    GTF -> GTF
    EQF -> case compareF x y of
              LTF -> LTF
              GTF -> GTF
              EQF -> EQF

instance OrdF f => OrdF (Assignment f) where
  compareF x y = compareAsgn (view x) (view y)

instance OrdF f => Ord (Assignment f ctx) where
  compare x y = toOrdering (compareF x y)

instance HashableF f => HashableF (Assignment f) where
  hashWithSaltF = hashWithSalt

instance HashableF f => Hashable (AssignView f ctx) where
  hashWithSalt s AssignEmpty = s
  hashWithSalt s (AssignExtend asgn x) = (s `hashWithSalt` asgn) `hashWithSaltF` x

instance HashableF f => Hashable (Assignment f ctx) where
  hashWithSalt s = hashWithSalt s . view

instance ShowF f => ShowF (Assignment f) where
  showF a = "[" ++ intercalate ", " (toList showF a) ++ "]"

instance ShowF f => Show (Assignment f ctx) where
  show a = showF a

instance FunctorFC Assignment where
  fmapFC = fmapFCDefault

instance FoldableFC Assignment where
  foldMapFC = foldMapFCDefault

instance TraversableFC Assignment where
  traverseFC = traverseF

traverseF :: forall (f:: k -> *) (g::k -> *) (m:: * -> *) (c::Ctx k)
           . Applicative m
          => (forall tp . f tp -> m (g tp))
          -> Assignment f c
          -> m (Assignment g c)
traverseF f (Assignment a) = Assignment <$> traverse (\x -> toAny <$> f (fromAny x)) a

-- | Convert assignment to list.
toList :: (forall tp . f tp -> a)
       -> Assignment f c
       -> [a]
toList = toListFC

zipWithM :: Applicative m
         => (forall tp . f tp -> g tp -> m (h tp))
         -> Assignment f c
         -> Assignment g c
         -> m (Assignment h c)
zipWithM f (Assignment x) (Assignment y) =
   Assignment <$> traverse (\(a,b) -> toAny <$> f (fromAny a) (fromAny b)) (Seq.zip x y)

zipWith :: (forall x . f x -> g x -> h x)
        -> Assignment f a
        -> Assignment g a
        -> Assignment h a
zipWith f = \x y -> runIdentity $ zipWithM (\u v -> pure (f u v)) x y
{-# INLINE zipWith #-}

(%>) :: Assignment f x -> f tp -> Assignment f (x '::> tp)
a %> v = extend a v

traverseWithIndex :: Applicative m
                  => (forall tp . Index ctx tp -> f tp -> m (g tp))
                  -> Assignment f ctx
                  -> m (Assignment g ctx)
traverseWithIndex f a = generateM (size a) $ \i -> f i (a ! i)

------------------------------------------------------------------------
-- Lens combinators

unsafeLens :: Int -> Lens.Lens (Assignment f ctx) (Assignment f ctx') (f tp) (f u)
unsafeLens idx =
  Lens.lens (! (Index idx))
            (\(Assignment a) x -> Assignment $ Seq.update idx (toAny x) a)

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

{-
------------------------------------------------------------------------
-- Test code

newtype C tp = C Int

instance ShowF C where
  showF (C i) = show i

test5= empty %> C 0 %> C 1 %> C 2 %> C 3 %> C 4
test7 = test5 %> C 5 %> C 6


test9 :: Int -> Int
test9 c = tsize $ unsafe_bin_generate c 0 (\i -> C (indexVal i))
-}
