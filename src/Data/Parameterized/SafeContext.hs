------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.SafeContext
-- Description      : Finite dependent products
-- Copyright        : (c) Galois, Inc 2014
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
-- Stability        : provisional
--
-- This module defines type contexts as a data-kind that consists of
-- a list of types.  Indexes are defined with respect to these contexts.
-- In addition, finite dependent products (Assignements) are defined over
-- type contexts.  The elements of an assignment can be accessed using
-- appropriately-typed indices.
--
-- This implementation is entirely typesafe, and provides a proof that
-- the signature implemented by this module is consistent.  Contexts,
-- indexes, and assignements are represented naively by linear sequences.
--
-- Compared to the implementation in UnsafeTypeContext, this one suffers
-- from the fact that the operation of extending an the context of an index
-- is _not_ a no-op.  We therefore cannot use Data.Coerce.coerce to understand
-- indexes in a new context without actually breaking things.
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
{-# LANGUAGE TypeOperators #-}
module Data.Parameterized.SafeContext
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
import Data.List (intercalate)
import Data.Maybe (listToMaybe)
import Data.Type.Equality
import Prelude hiding (init, map, succ, (!!))

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative(..))
#endif

import Data.Parameterized.Classes
import Data.Parameterized.Ctx
import Data.Parameterized.TraversableFC

------------------------------------------------------------------------
-- Size

-- | Represents the size of a context.
data Size (ctx :: Ctx k) where
  SizeZero :: Size 'EmptyCtx
  SizeSucc :: Size ctx -> Size (ctx '::> tp)

sizeInt :: Size ctx -> Int
sizeInt SizeZero = 0
sizeInt (SizeSucc sz) = (+1) $! sizeInt sz

-- | The size of an empty context.
zeroSize :: Size 'EmptyCtx
zeroSize = SizeZero

-- | Increment the size to the next value.
incSize :: Size ctx -> Size (ctx '::> tp)
incSize sz = SizeSucc sz

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
data Diff (l :: Ctx k) (r :: Ctx k) where
  DiffHere :: Diff ctx ctx
  DiffThere :: Diff ctx1 ctx2 -> Diff ctx1 (ctx2 '::> tp)

-- | The identity difference.
noDiff :: Diff l l
noDiff = DiffHere

-- | Extend the difference to a sub-context of the right side.
extendRight :: Diff l r -> Diff l (r '::> tp)
extendRight diff = DiffThere diff

composeDiff :: Diff a b -> Diff b c -> Diff a c
composeDiff x DiffHere = x
composeDiff x (DiffThere y) = DiffThere (composeDiff x y)

instance Cat.Category Diff where
  id = DiffHere
  d1 . d2 = composeDiff d2 d1

-- | Extend the size by a given difference.
extSize :: Size l -> Diff l r -> Size r
extSize sz DiffHere = sz
extSize sz (DiffThere diff) = incSize (extSize sz diff)

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
data Index (ctx :: Ctx k) (tp :: k) where
  IndexHere :: Size ctx -> Index (ctx '::> tp) tp
  IndexThere :: Index ctx tp -> Index (ctx '::> tp') tp

indexVal :: Index ctx tp -> Int
indexVal (IndexHere sz) = sizeInt sz
indexVal (IndexThere idx) = indexVal idx

instance Eq (Index ctx tp) where
  idx1 == idx2 = isJust (testEquality idx1 idx2)

instance TestEquality (Index ctx) where
  testEquality (IndexHere _) (IndexHere _) = Just Refl
  testEquality (IndexHere _) (IndexThere _) = Nothing
  testEquality (IndexThere _) (IndexHere _) = Nothing
  testEquality (IndexThere idx1) (IndexThere idx2) =
     case testEquality idx1 idx2 of
         Just Refl -> Just Refl
         Nothing -> Nothing

instance Ord (Index ctx tp) where
  compare i j = toOrdering (compareF i j)

instance OrdF (Index ctx) where
  compareF (IndexHere _) (IndexHere _) = EQF
  compareF (IndexThere _) (IndexHere _) = LTF
  compareF (IndexHere _) (IndexThere _) = GTF
  compareF (IndexThere idx1) (IndexThere idx2) =
     case compareF idx1 idx2 of
        EQF -> EQF
        LTF -> LTF
        GTF -> GTF

-- | Index for first element in context.
base :: Index ('EmptyCtx '::> tp) tp
base = IndexHere SizeZero

-- | Increase context while staying at same index.
skip :: Index ctx x -> Index (ctx '::> y) x
skip idx = IndexThere idx

_indexSize :: Index ctx tp -> Size ctx
_indexSize (IndexHere sz) = SizeSucc sz
_indexSize (IndexThere idx) = SizeSucc (_indexSize idx)

-- | Return the index of a element one past the size.
nextIndex :: Size ctx -> Index (ctx '::> tp) tp
nextIndex sz = IndexHere sz

{-# INLINE extendIndex #-}
extendIndex :: KnownDiff l r => Index l tp -> Index r tp
extendIndex = extendIndex' knownDiff

{-# INLINE extendIndex' #-}
extendIndex' :: Diff l r -> Index l tp -> Index r tp
extendIndex' DiffHere idx = idx
extendIndex' (DiffThere diff) idx = IndexThere (extendIndex' diff idx)

-- | Given a size @n@, an initial value @v0@, and a function @f@, @forIndex n v0 f@,
-- calls @f@ on each index less than @n@ starting from @0@ and @v0@, with the value @v@ obtained
-- from the last call.
forIndex :: forall ctx r
          . Size ctx
         -> (forall tp . r -> Index ctx tp -> r)
         -> r
         -> r
forIndex sz_top f = go id sz_top
 where go :: forall ctx'. (forall tp. Index ctx' tp -> Index ctx tp) -> Size ctx' -> r -> r
       go _ SizeZero = id
       go g (SizeSucc sz) = \r -> go (\i -> g (IndexThere i)) sz  $ f r (g (IndexHere sz))


data SomeIndex ctx where
  SomeIndex :: Index ctx tp -> SomeIndex ctx

indexList :: forall ctx. Size ctx -> [SomeIndex ctx]
indexList sz_top = go id [] sz_top
 where go :: (forall tp. Index ctx' tp -> Index ctx tp) -> [SomeIndex ctx] -> Size ctx' -> [SomeIndex ctx]
       go _ ls SizeZero       = ls
       go g ls (SizeSucc sz)  = go (\i -> g (IndexThere i)) (SomeIndex (g (IndexHere sz)) : ls) sz

-- | Return index at given integer or nothing if integer is out of bounds.
intIndex :: Int -> Size ctx -> Maybe (SomeIndex ctx)
intIndex n sz = listToMaybe $ drop n $ indexList sz

instance Show (Index ctx tp) where
   show = show . indexVal

instance ShowF (Index ctx) where
   showF = show

------------------------------------------------------------------------
-- Assignment

data Assignment (f :: k -> *) (c :: Ctx k) where
  AssignEmpty  :: Assignment f 'EmptyCtx
  AssignCons   :: Assignment f ctx -> f tp -> Assignment f (ctx '::> tp)
  AssignMap    :: forall f g ctx
                . (forall tp . f tp -> g tp)
               -> Assignment f ctx
               -> Assignment g ctx


instance NFData (Assignment f ctx) where
  rnf AssignEmpty = ()
  rnf (AssignCons asgn x) = rnf asgn `seq` x `seq` ()
  rnf (AssignMap _ asgn) = rnf asgn `seq` ()

size :: Assignment f ctx -> Size ctx
size AssignEmpty = SizeZero
size (AssignCons asgn _) = SizeSucc (size asgn)
size (AssignMap _ asgn) = size asgn

-- | Generate an assignment
generate :: forall ctx f
          . Size ctx
         -> (forall tp . Index ctx tp -> f tp)
         -> Assignment f ctx
generate sz_top f = go id sz_top
 where go :: forall ctx'
           . (forall tp. Index ctx' tp -> Index ctx tp)
          -> Size ctx'
          -> Assignment f ctx'
       go _ SizeZero = AssignEmpty
       go g (SizeSucc sz) =
            let ctx = go (\i -> g (IndexThere i)) sz
                x = f (g (IndexHere sz))
             in AssignCons ctx x

-- | Generate an assignment
generateM :: forall ctx m f
           . Monad m
          => Size ctx
          -> (forall tp . Index ctx tp -> m (f tp))
          -> m (Assignment f ctx)
generateM sz_top f = go id sz_top
 where go :: forall ctx'. (forall tp. Index ctx' tp -> Index ctx tp) -> Size ctx' -> m (Assignment f ctx')
       go _ SizeZero = return AssignEmpty
       go g (SizeSucc sz) = do
             asgn <- go (\i -> g (IndexThere i)) sz
             x <- f (g (IndexHere sz))
             return $ AssignCons asgn x

-- | Create empty indexec vector.
empty :: Assignment f 'EmptyCtx
empty = AssignEmpty

extend :: Assignment f ctx -> f tp -> Assignment f (ctx '::> tp)
extend asgn e = AssignCons asgn e

update :: Index ctx tp -> f tp -> Assignment f ctx -> Assignment f ctx
update idx e asgn = adjust (\_ -> e) idx asgn

adjust :: forall f ctx tp. (f tp -> f tp) -> Index ctx tp -> Assignment f ctx -> Assignment f ctx
adjust f = go (\x -> x)
 where
  go :: (forall tp'. g tp' -> f tp') -> Index ctx' tp -> Assignment g ctx' -> Assignment f ctx'
  go g idx (AssignMap g' asgn) = go (\x -> (g (g' x))) idx asgn
  go g (IndexHere _)    (AssignCons asgn x) = AssignCons (AssignMap g asgn) (f (g x))
  go g (IndexThere idx) (AssignCons asgn x) = AssignCons (go g idx asgn) (g x)
--  go _ (IndexHere _) AssignEmpty = undefined
--  go _ (IndexThere _) AssignEmpty = undefined
  go _ _ _ = error "SafeTypeContext.adjust: impossible!"

-- | Return assignment with all but the last block.
init :: Assignment f (ctx '::> tp) -> Assignment f ctx
init (AssignCons asgn _) = asgn
init _ = error "Data.Parameterized.SafeContext.init: impossible!"

idxlookup :: (forall tp. a tp -> b tp) -> Assignment a ctx -> forall tp. Index ctx tp -> b tp
idxlookup f (AssignCons _   x) (IndexHere _) = f x
idxlookup f (AssignCons ctx _) (IndexThere idx) = idxlookup f ctx idx
idxlookup f (AssignMap g ctx) idx = idxlookup (\x -> f (g x)) ctx idx
idxlookup _ AssignEmpty _ = error "Data.Parameterized.SafeContext.lookup: impossible case"

-- | Return value of assignment.
(!) :: Assignment f ctx -> Index ctx tp -> f tp
(!) asgn idx = idxlookup id asgn idx

-- | Return value of assignment.
(!!) :: KnownDiff l r => Assignment f r -> Index l tp -> f tp
a !! i = a ! extendIndex i

instance TestEquality f => Eq (Assignment f ctx) where
  x == y = isJust (testEquality x y)

simplAssign :: (forall tp. a tp -> b tp) -> forall tp. Assignment a tp -> Assignment b tp
simplAssign _ AssignEmpty = AssignEmpty
simplAssign f (AssignCons asgn x) = AssignCons (simplAssign f asgn) (f x)
simplAssign f (AssignMap g asgn) = simplAssign (\x -> f (g x)) asgn

testEq :: TestEquality f => Assignment f cxt1 -> Assignment f cxt2 -> Maybe (cxt1 :~: cxt2)
testEq AssignEmpty AssignEmpty = Just Refl
testEq (AssignCons ctx1 x1) (AssignCons ctx2 x2) =
     case testEq ctx1 ctx2 of
       Nothing -> Nothing
       Just Refl ->
          case testEquality x1 x2 of
             Nothing -> Nothing
             Just Refl -> Just Refl
testEq _ _ = error "Data.Parameterized.SafeContext.testEquality: impossible!"


instance TestEquality f => TestEquality (Assignment f) where
   testEquality x y = testEq (simplAssign id x) (simplAssign id y)

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
  traverseFC _ AssignEmpty = pure AssignEmpty
  traverseFC f (AssignCons asgn x) = pure AssignCons <*> traverseF f asgn <*> f x
  traverseFC f (AssignMap g asgn) = traverseF (\x -> f (g x)) asgn

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

traverseF :: forall f g m c
           . Applicative m
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
zipWithM f x y = go (simplAssign id x) (simplAssign id y)
 where go AssignEmpty AssignEmpty = return AssignEmpty
       go (AssignCons asgn1 x1) (AssignCons asgn2 x2) = do
           asgn' <- zipWithM f asgn1 asgn2
           x' <- f x1 x2
           return $ AssignCons asgn' x'
       go _ _ = error "Data.Parameterized.SafeContext.zipWithM: impossible!"

(%>) :: Assignment f x -> f tp -> Assignment f (x '::> tp)
a %> v = extend a v