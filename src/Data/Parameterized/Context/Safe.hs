------------------------------------------------------------------------
-- |
-- Module           : Data.Parameterized.Context.Safe
-- Copyright        : (c) Galois, Inc 2014-2015
-- Maintainer       : Joe Hendrix <jhendrix@galois.com>
--
-- This module defines type contexts as a data-kind that consists of
-- a list of types.  Indexes are defined with respect to these contexts.
-- In addition, finite dependent products (Assignments) are defined over
-- type contexts.  The elements of an assignment can be accessed using
-- appropriately-typed indexes.
--
-- This module is intended to export exactly the same API as module
-- "Data.Parameterized.Context.Unsafe", so that they can be used
-- interchangeably.
--
-- This implementation is entirely typesafe, and provides a proof that
-- the signature implemented by this module is consistent.  Contexts,
-- indexes, and assignments are represented naively by linear sequences.
--
-- Compared to the implementation in "Data.Parameterized.Context.Unsafe",
-- this one suffers from the fact that the operation of extending an
-- the context of an index is /not/ a no-op. We therefore cannot use
-- 'Data.Coerce.coerce' to understand indexes in a new context without
-- actually breaking things.
--------------------------------------------------------------------------
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_HADDOCK hide #-}
module Data.Parameterized.Context.Safe
  ( module Data.Parameterized.Ctx
    -- * Size
  , Size
  , sizeInt
  , zeroSize
  , incSize
  , decSize
  , extSize
  , addSize
  , SizeView(..)
  , viewSize
  , sizeToNatRepr
  , KnownContext(..)
    -- * Diff
  , Diff
  , noDiff
  , addDiff
  , extendRight
  , appendDiff
  , DiffView(..)
  , viewDiff
  , KnownDiff(..)
  , IsAppend(..)
  , diffIsAppend
    -- * Indexing
  , Index
  , indexVal
  , baseIndex
  , skipIndex
  , lastIndex
  , nextIndex
  , leftIndex
  , rightIndex
  , extendIndex
  , extendIndex'
  , extendIndexAppendLeft
  , forIndex
  , forIndexRange
  , intIndex
  , IndexView(..)
  , viewIndex
    -- * Assignments
  , Assignment
  , size
  , Data.Parameterized.Context.Safe.replicate
  , generate
  , generateM
  , empty
  , extend
  , adjust
  , update
  , adjustM
  , AssignView(..)
  , viewAssign
  , (!)
  , (!^)
  , zipWith
  , zipWithM
  , (<++>)
  , traverseWithIndex
  ) where

import qualified Control.Category as Cat
import Control.DeepSeq
import qualified Control.Lens as Lens
import Control.Monad.Identity (Identity(..))
import Data.Hashable
import Data.List (intercalate)
import Data.Maybe (listToMaybe)
import Data.Type.Equality
import Prelude hiding (init, map, null, replicate, succ, zipWith)
import Data.Kind(Type)

import Data.Parameterized.Classes
import Data.Parameterized.Ctx
import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.Parameterized.TraversableFC.WithIndex

------------------------------------------------------------------------
-- Size

-- | An indexed singleton type representing the size of a context.
data Size (ctx :: Ctx k) where
  SizeZero :: Size 'EmptyCtx
  SizeSucc :: !(Size ctx) -> Size (ctx '::> tp)

-- | Renders as integer literal
instance Show (Size ctx) where
  show = show . sizeInt

instance ShowF Size

-- | Convert a context size to an 'Int'.
sizeInt :: Size ctx -> Int
sizeInt SizeZero = 0
sizeInt (SizeSucc sz) = (+1) $! sizeInt sz

-- | The size of an empty context.
zeroSize :: Size 'EmptyCtx
zeroSize = SizeZero

-- | Increment the size to the next value.
incSize :: Size ctx -> Size (ctx '::> tp)
incSize sz = SizeSucc sz

decSize :: Size (ctx '::> tp) -> Size ctx
decSize (SizeSucc sz) = sz

-- | The total size of two concatenated contexts.
addSize :: Size x -> Size y -> Size (x <+> y)
addSize sx SizeZero = sx
addSize sx (SizeSucc sy) = SizeSucc (addSize sx sy)

-- | Allows interpreting a size.
data SizeView (ctx :: Ctx k) where
  ZeroSize :: SizeView 'EmptyCtx
  IncSize :: !(Size ctx) -> SizeView (ctx '::> tp)

-- | View a size as either zero or a smaller size plus one.
viewSize :: Size ctx -> SizeView ctx
viewSize SizeZero = ZeroSize
viewSize (SizeSucc s) = IncSize s

-- | Convert a 'Size' into a 'NatRepr'.
sizeToNatRepr :: Size items -> NatRepr (CtxSize items)
sizeToNatRepr sz =
  case viewSize sz of
    ZeroSize -> knownRepr
    IncSize sz' ->
      let oldRep = sizeToNatRepr sz'
      in case plusComm (knownRepr :: NatRepr 1) oldRep of
           Refl -> incNat oldRep

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

-- | The identity difference. Identity element of 'Category' instance.
noDiff :: Diff l l
noDiff = DiffHere

-- | The addition of differences. Flipped binary operation
-- of 'Category' instance.
addDiff :: Diff a b -> Diff b c -> Diff a c
addDiff x DiffHere = x
addDiff x (DiffThere y) = DiffThere (addDiff x y)

-- | Extend the difference to a sub-context of the right side.
extendRight :: Diff l r -> Diff l (r '::> tp)
extendRight diff = DiffThere diff

appendDiff :: Size r -> Diff l (l <+> r)
appendDiff SizeZero = DiffHere
appendDiff (SizeSucc sz) = DiffThere (appendDiff sz)

-- | Implemented with 'noDiff' and 'addDiff'
instance Cat.Category Diff where
  id = DiffHere
  d1 . d2 = addDiff d2 d1

-- | Extend the size by a given difference.
extSize :: Size l -> Diff l r -> Size r
extSize sz DiffHere = sz
extSize sz (DiffThere diff) = incSize (extSize sz diff)

-- | Proof that @r = l <+> app@ for some @app@
data IsAppend l r where
  IsAppend :: Size app -> IsAppend l (l <+> app)

-- | If @l@ is a sub-context of @r@ then extract out their "contextual
-- difference", i.e., the @app@ such that @r = l <+> app@
diffIsAppend :: Diff l r -> IsAppend l r
diffIsAppend DiffHere = IsAppend zeroSize
diffIsAppend (DiffThere diff) =
  case diffIsAppend diff of
    IsAppend sz -> IsAppend (incSize sz)

data DiffView a b where
  NoDiff :: DiffView a a
  ExtendRightDiff :: Diff a b -> DiffView a (b ::> r)

viewDiff :: Diff a b -> DiffView a b
viewDiff DiffHere = NoDiff
viewDiff (DiffThere diff) = ExtendRightDiff diff

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
  IndexThere :: !(Index ctx tp) -> Index (ctx '::> tp') tp

-- | Convert an index to an 'Int', where the index of the left-most type in the context is 0.
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
  compareF (IndexThere idx1) (IndexThere idx2) = lexCompareF idx1 idx2 $ EQF

-- | Index for first element in context.
baseIndex :: Index ('EmptyCtx '::> tp) tp
baseIndex = IndexHere SizeZero

-- | Increase context while staying at same index.
skipIndex :: Index ctx x -> Index (ctx '::> y) x
skipIndex idx = IndexThere idx

-- | Return the index of an element one past the size.
nextIndex :: Size ctx -> Index (ctx '::> tp) tp
nextIndex sz = IndexHere sz

-- | Return the last index of a element.
lastIndex :: Size (ctx ::> tp) -> Index (ctx ::> tp) tp
lastIndex (SizeSucc s) = IndexHere s

-- | Adapts an index in the left hand context of an append operation.
leftIndex :: Size r -> Index l tp -> Index (l <+> r) tp
leftIndex sr il = extendIndex' (appendDiff sr) il

-- | Adapts an index in the right hand context of an append operation.
rightIndex :: Size l -> Size r -> Index r tp -> Index (l <+> r) tp
rightIndex sl sr ir =
  case viewIndex sr ir of
    IndexViewInit i -> skipIndex (rightIndex sl (decSize sr) i)
    IndexViewLast s -> lastIndex (incSize (addSize sl s))

{-# INLINE extendIndex #-}
extendIndex :: KnownDiff l r => Index l tp -> Index r tp
extendIndex = extendIndex' knownDiff

{-# INLINE extendIndex' #-}
-- | Compute an 'Index' into a context @r@ from an 'Index' into
-- a sub-context @l@ of @r@.
extendIndex' :: Diff l r -> Index l tp -> Index r tp
extendIndex' DiffHere idx = idx
extendIndex' (DiffThere diff) idx = IndexThere (extendIndex' diff idx)

{-# INLINE extendIndexAppendLeft #-}
-- | Compute an 'Index' into an appended context from an 'Index' into
-- its suffix.
extendIndexAppendLeft :: Size l -> Size r -> Index r tp -> Index (l <+> r) tp
extendIndexAppendLeft sz sz' idx = case viewIndex sz' idx of
  IndexViewLast _ -> lastIndex (addSize sz sz')
  IndexViewInit idx' -> skipIndex (extendIndexAppendLeft sz (decSize sz') idx')

-- | Given a size @n@, a function @f@, and an initial value @v0@, the
-- expression @forIndex n f v0@ calls @f@ on each index less than @n@
-- starting from @0@ and @v0@, with the value @v@ obtained from the
-- last call.
forIndex :: forall ctx r
          . Size ctx
         -> (forall tp . r -> Index ctx tp -> r)
         -> r
         -> r
forIndex sz_top f = go id sz_top
 where go :: forall ctx'. (forall tp. Index ctx' tp -> Index ctx tp) -> Size ctx' -> r -> r
       go _ SizeZero = id
       go g (SizeSucc sz) = \r -> go (\i -> g (IndexThere i)) sz  $ f r (g (IndexHere sz))

data LDiff (l :: Ctx k) (r :: Ctx k) where
 LDiffHere :: LDiff a a
 LDiffThere :: !(LDiff (a::>x) b) -> LDiff a b

ldiffIndex :: Index a tp -> LDiff a b -> Index b tp
ldiffIndex i LDiffHere = i
ldiffIndex i (LDiffThere d) = ldiffIndex (IndexThere i) d

forIndexLDiff :: Size a
              -> LDiff a b
              -> (forall tp . Index b tp -> r -> r)
              -> r
              -> r
forIndexLDiff _ LDiffHere _ r = r
forIndexLDiff sz (LDiffThere d) f r =
  forIndexLDiff (SizeSucc sz) d f (f (ldiffIndex (IndexHere sz) d) r)

forIndexRangeImpl :: Int
                  -> Size a
                  -> LDiff a b
                  -> (forall tp . Index b tp -> r -> r)
                  -> r
                  -> r
forIndexRangeImpl 0 sz d f r = forIndexLDiff sz d f r
forIndexRangeImpl _ SizeZero _ _ r = r
forIndexRangeImpl i (SizeSucc sz) d f r =
  forIndexRangeImpl (i-1) sz (LDiffThere d) f r

-- | Given an index @i@, size @n@, a function @f@, and a value @v@,
-- the expression @forIndexRange i n f v@ is equivalent
-- to @v@ when @i >= sizeInt n@, and @f i (forIndexRange (i+1) n f v)@
-- otherwise.
forIndexRange :: Int
              -> Size ctx
              -> (forall tp . Index ctx tp -> r -> r)
              -> r
              -> r
forIndexRange i sz f r = forIndexRangeImpl i sz LDiffHere f r

indexList :: forall ctx. Size ctx -> [Some (Index ctx)]
indexList sz_top = go id [] sz_top
 where go :: (forall tp. Index ctx' tp -> Index ctx tp)
          -> [Some (Index ctx)]
          -> Size ctx'
          -> [Some (Index ctx)]
       go _ ls SizeZero       = ls
       go g ls (SizeSucc sz)  = go (\i -> g (IndexThere i)) (Some (g (IndexHere sz)) : ls) sz

-- | Return index at given integer or nothing if integer is out of bounds.
intIndex :: Int -> Size ctx -> Maybe (Some (Index ctx))
intIndex n sz = listToMaybe $ drop n $ indexList sz

-- | Renders as integer literal
instance Show (Index ctx tp) where
   show = show . indexVal

instance ShowF (Index ctx)

-- | View of indexes as pointing to the last element in the
-- index range or pointing to an earlier element in a smaller
-- range.
data IndexView ctx tp where
  IndexViewLast :: Size  ctx   -> IndexView (ctx '::> t) t
  IndexViewInit :: Index ctx t -> IndexView (ctx '::> u) t

instance ShowF (IndexView ctx)
deriving instance Show (IndexView ctx tp)

-- | Project an index
viewIndex :: Size ctx -> Index ctx tp -> IndexView ctx tp
viewIndex _ (IndexHere sz) = IndexViewLast sz
viewIndex _ (IndexThere i) = IndexViewInit i
-- NB: the unused size parameter is needed in the Unsafe module

------------------------------------------------------------------------
-- Assignment

-- | An assignment is a sequence that maps each index with type 'tp' to
-- a value of type 'f tp'.
data Assignment (f :: k -> Type) (ctx :: Ctx k) where
  AssignmentEmpty :: Assignment f EmptyCtx
  AssignmentExtend :: Assignment f ctx -> f tp -> Assignment f (ctx ::> tp)

-- | View an assignment as either empty or an assignment with one appended.
data AssignView (f :: k -> Type) (ctx :: Ctx k) where
  AssignEmpty :: AssignView f EmptyCtx
  AssignExtend :: Assignment f ctx -> f tp -> AssignView f (ctx::>tp)

viewAssign :: forall f ctx . Assignment f ctx -> AssignView f ctx
viewAssign AssignmentEmpty = AssignEmpty
viewAssign (AssignmentExtend asgn x) = AssignExtend asgn x

instance NFData (Assignment f ctx) where
  rnf AssignmentEmpty = ()
  rnf (AssignmentExtend asgn x) = rnf asgn `seq` x `seq` ()

-- | Return number of elements in assignment.
size :: Assignment f ctx -> Size ctx
size AssignmentEmpty = SizeZero
size (AssignmentExtend asgn _) = SizeSucc (size asgn)

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
       go _ SizeZero = AssignmentEmpty
       go g (SizeSucc sz) =
            let ctx = go (\i -> g (IndexThere i)) sz
                x = f (g (IndexHere sz))
             in AssignmentExtend ctx x

-- | Generate an assignment
generateM :: forall ctx m f
           . Applicative m
          => Size ctx
          -> (forall tp . Index ctx tp -> m (f tp))
          -> m (Assignment f ctx)
generateM sz_top f = go id sz_top
 where go :: forall ctx'. (forall tp. Index ctx' tp -> Index ctx tp) -> Size ctx' -> m (Assignment f ctx')
       go _ SizeZero = pure AssignmentEmpty
       go g (SizeSucc sz) =
             AssignmentExtend <$> (go (\i -> g (IndexThere i)) sz) <*> f (g (IndexHere sz))

-- | @replicate n@ make a context with different copies of the same
-- polymorphic value.
replicate :: Size ctx -> (forall tp . f tp) -> Assignment f ctx
replicate n c = generate n (\_ -> c)

-- | Create empty indexed vector.
empty :: Assignment f 'EmptyCtx
empty = AssignmentEmpty

-- n.b. see 'singleton' in Data/Parameterized/Context.hs

-- | Extend an indexed vector with a new entry.
extend :: Assignment f ctx -> f tp -> Assignment f (ctx '::> tp)
extend asgn e = AssignmentExtend asgn e

{-# DEPRECATED adjust "Replace 'adjust f i asgn' with 'Lens.over (ixF i) f asgn' instead." #-}
adjust :: forall f ctx tp. (f tp -> f tp) -> Index ctx tp -> Assignment f ctx -> Assignment f ctx
adjust f idx asgn = runIdentity (adjustM (Identity . f) idx asgn)

{-# DEPRECATED update "Replace 'update idx val asgn' with 'Lens.set (ixF idx) val asgn' instead." #-}
update :: forall f ctx tp. Index ctx tp -> f tp -> Assignment f ctx -> Assignment f ctx
update i v a = adjust (\_ -> v) i a

adjustM :: forall m f ctx tp. Functor m => (f tp -> m (f tp)) -> Index ctx tp -> Assignment f ctx -> m (Assignment f ctx)
adjustM f = go (\x -> x)
 where
  go :: (forall tp'. g tp' -> f tp') -> Index ctx' tp -> Assignment g ctx' -> m (Assignment f ctx')
  go g (IndexHere _)     (AssignmentExtend asgn x) = AssignmentExtend (map g asgn) <$> f (g x)
  go g (IndexThere idx)  (AssignmentExtend asgn x) = flip AssignmentExtend (g x)   <$> go g idx asgn

type instance IndexF   (Assignment (f :: k -> Type) ctx) = Index ctx
type instance IxValueF (Assignment (f :: k -> Type) ctx) = f

instance forall k (f :: k -> Type) ctx. IxedF k (Assignment f ctx) where
  ixF :: Index ctx x -> Lens.Traversal' (Assignment f ctx) (f x)
  ixF idx f = adjustM f idx

instance forall k (f :: k -> Type) ctx. IxedF' k (Assignment f ctx) where
  ixF' :: Index ctx x -> Lens.Lens' (Assignment f ctx) (f x)
  ixF' idx f = adjustM f idx

idxlookup :: (forall tp. a tp -> b tp) -> Assignment a ctx -> forall tp. Index ctx tp -> b tp
idxlookup f (AssignmentExtend _   x) (IndexHere _) = f x
idxlookup f (AssignmentExtend ctx _) (IndexThere idx) = idxlookup f ctx idx
idxlookup _ AssignmentEmpty idx = case idx of {}

-- | Return value of assignment.
(!) :: Assignment f ctx -> Index ctx tp -> f tp
(!) asgn idx = idxlookup id asgn idx

-- | Return value of assignment, where the index is into an
--   initial sequence of the assignment.
(!^) :: KnownDiff l r => Assignment f r -> Index l tp -> f tp
a !^ i = a ! extendIndex i

instance TestEquality f => Eq (Assignment f ctx) where
  x == y = isJust (testEquality x y)

testEq :: (forall x y. f x -> f y -> Maybe (x :~: y))
       -> Assignment f cxt1 -> Assignment f cxt2 -> Maybe (cxt1 :~: cxt2)
testEq _ AssignmentEmpty AssignmentEmpty = Just Refl
testEq test (AssignmentExtend ctx1 x1) (AssignmentExtend ctx2 x2) =
     case testEq test ctx1 ctx2 of
       Nothing -> Nothing
       Just Refl ->
          case test x1 x2 of
             Nothing -> Nothing
             Just Refl -> Just Refl
testEq _ AssignmentEmpty AssignmentExtend{} = Nothing
testEq _ AssignmentExtend{} AssignmentEmpty = Nothing

instance TestEqualityFC Assignment where
   testEqualityFC f = testEq f
instance TestEquality f => TestEquality (Assignment f) where
   testEquality x y = testEq testEquality x y
instance TestEquality f => PolyEq (Assignment f x) (Assignment f y) where
  polyEqF x y = fmap (\Refl -> Refl) $ testEquality x y

compareAsgn :: (forall x y. f x -> f y -> OrderingF x y)
            -> Assignment f ctx1 -> Assignment f ctx2 -> OrderingF ctx1 ctx2
compareAsgn _ AssignmentEmpty AssignmentEmpty = EQF
compareAsgn _ AssignmentEmpty _ = GTF
compareAsgn _ _ AssignmentEmpty = LTF
compareAsgn test (AssignmentExtend ctx1 x) (AssignmentExtend ctx2 y) =
  case compareAsgn test ctx1 ctx2 of
    LTF -> LTF
    GTF -> GTF
    EQF -> case test x y of
              LTF -> LTF
              GTF -> GTF
              EQF -> EQF

instance OrdFC Assignment where
  compareFC f = compareAsgn f

instance OrdF f => OrdF (Assignment f) where
  compareF = compareAsgn compareF

instance OrdF f => Ord (Assignment f ctx) where
  compare x y = toOrdering (compareF x y)


instance Hashable (Index ctx tp) where
  hashWithSalt = hashWithSaltF
instance HashableF (Index ctx) where
  hashWithSaltF s i = hashWithSalt s (indexVal i)

instance (HashableF f, TestEquality f) => HashableF (Assignment f) where
  hashWithSaltF = hashWithSalt

instance (HashableF f, TestEquality f) => Hashable (Assignment f ctx) where
  hashWithSalt s AssignmentEmpty = s
  hashWithSalt s (AssignmentExtend asgn x) = (s `hashWithSalt` asgn) `hashWithSaltF` x

instance ShowF f => Show (Assignment f ctx) where
  show a = "[" ++ intercalate ", " (toList showF a) ++ "]"

instance ShowF f => ShowF (Assignment f)

instance FunctorFC Assignment where
  fmapFC = fmapFCDefault

instance FoldableFC Assignment where
  foldMapFC = foldMapFCDefault

instance TraversableFC Assignment where
  traverseFC f = traverseF f

instance FunctorFCWithIndex Assignment where
  imapFC = imapFCDefault

instance FoldableFCWithIndex Assignment where
  ifoldMapFC = ifoldMapFCDefault

instance TraversableFCWithIndex Assignment where
  itraverseFC = traverseWithIndex

-- | Map assignment
map :: (forall tp . f tp -> g tp) -> Assignment f c -> Assignment g c
map f = fmapFC f

traverseF :: forall k (f:: k -> Type) (g::k -> Type) (m:: Type -> Type) (c::Ctx k)
           . Applicative m
          => (forall tp . f tp -> m (g tp))
          -> Assignment f c
          -> m (Assignment g c)
traverseF _ AssignmentEmpty = pure AssignmentEmpty
traverseF f (AssignmentExtend asgn x) = pure AssignmentExtend <*> traverseF f asgn <*> f x

-- | Convert assignment to list.
toList :: (forall tp . f tp -> a)
       -> Assignment f c
       -> [a]
toList f = toListFC f

zipWithM :: Applicative m
         => (forall tp . f tp -> g tp -> m (h tp))
         -> Assignment f c
         -> Assignment g c
         -> m (Assignment h c)
zipWithM f x y = go x y
 where go AssignmentEmpty AssignmentEmpty = pure AssignmentEmpty
       go (AssignmentExtend asgn1 x1) (AssignmentExtend asgn2 x2) =
             AssignmentExtend <$> (zipWithM f asgn1 asgn2) <*> (f x1 x2)

zipWith :: (forall x . f x -> g x -> h x)
        -> Assignment f a
        -> Assignment g a
        -> Assignment h a
zipWith f = \x y -> runIdentity $ zipWithM (\u v -> pure (f u v)) x y
{-# INLINE zipWith #-}

-- | This is a specialization of 'itraverseFC'.
traverseWithIndex :: Applicative m
                  => (forall tp . Index ctx tp -> f tp -> m (g tp))
                  -> Assignment f ctx
                  -> m (Assignment g ctx)
traverseWithIndex f a = generateM (size a) $ \i -> f i (a ! i)

(<++>) :: Assignment f x -> Assignment f y -> Assignment f (x <+> y)
x <++> AssignmentEmpty = x
x <++> AssignmentExtend y t = AssignmentExtend (x <++> y) t

------------------------------------------------------------------------
-- KnownRepr instances

instance (KnownRepr (Assignment f) ctx, KnownRepr f bt)
      => KnownRepr (Assignment f) (ctx ::> bt) where
  knownRepr = knownRepr `extend` knownRepr

instance KnownRepr (Assignment f) EmptyCtx where
  knownRepr = empty

--------------------------------------------------------------------------------------
-- lookups and update for lenses

data MyNat where
  MyZ :: MyNat
  MyS :: MyNat -> MyNat

type MyZ = 'MyZ
type MyS = 'MyS

data MyNatRepr :: MyNat -> Type where
  MyZR :: MyNatRepr MyZ
  MySR :: MyNatRepr n -> MyNatRepr (MyS n)

type family StrongCtxUpdate (n::MyNat) (ctx::Ctx k) (z::k) :: Ctx k where
  StrongCtxUpdate n       EmptyCtx     z = EmptyCtx
  StrongCtxUpdate MyZ     (ctx::>x)    z = ctx ::> z
  StrongCtxUpdate (MyS n) (ctx::>x)    z = (StrongCtxUpdate n ctx z) ::> x

type family MyNatLookup (n::MyNat) (ctx::Ctx k) (f::k -> Type) :: Type where
  MyNatLookup n       EmptyCtx  f = ()
  MyNatLookup MyZ     (ctx::>x) f = f x
  MyNatLookup (MyS n) (ctx::>x) f = MyNatLookup n ctx f

mynat_lookup :: MyNatRepr n -> Assignment f ctx -> MyNatLookup n ctx f
mynat_lookup _   AssignmentEmpty = ()
mynat_lookup MyZR     (AssignmentExtend _    x) = x
mynat_lookup (MySR n) (AssignmentExtend asgn _) = mynat_lookup n asgn

strong_ctx_update :: MyNatRepr n -> Assignment f ctx -> f tp -> Assignment f (StrongCtxUpdate n ctx tp)
strong_ctx_update _        AssignmentEmpty           _ = AssignmentEmpty
strong_ctx_update MyZR     (AssignmentExtend asgn _) z = AssignmentExtend asgn z
strong_ctx_update (MySR n) (AssignmentExtend asgn x) z = AssignmentExtend (strong_ctx_update n asgn z) x

------------------------------------------------------------------------
-- 1 field lens combinators

type Assignment1 f x1 = Assignment f ('EmptyCtx '::> x1)

instance Lens.Field1 (Assignment1 f t) (Assignment1 f u) (f t) (f u) where

  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR

------------------------------------------------------------------------
-- 2 field lens combinators

type Assignment2 f x1 x2
   = Assignment f ('EmptyCtx '::> x1 '::> x2)

instance Lens.Field1 (Assignment2 f t x2) (Assignment2 f u x2) (f t) (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field2 (Assignment2 f x1 t) (Assignment2 f x1 u) (f t) (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR


------------------------------------------------------------------------
-- 3 field lens combinators

type Assignment3 f x1 x2 x3
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3)

instance Lens.Field1 (Assignment3 f t x2 x3)
                     (Assignment3 f u x2 x3)
                     (f t)
                     (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MyZR

instance Lens.Field2 (Assignment3 f x1 t x3)
                     (Assignment3 f x1 u x3)
                     (f t)
                     (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field3 (Assignment3 f x1 x2 t)
                     (Assignment3 f x1 x2 u)
                     (f t)
                     (f u) where
  _3 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR

------------------------------------------------------------------------
-- 4 field lens combinators

type Assignment4 f x1 x2 x3 x4
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4)

instance Lens.Field1 (Assignment4 f t x2 x3 x4)
                     (Assignment4 f u x2 x3 x4)
                     (f t)
                     (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MyZR

instance Lens.Field2 (Assignment4 f x1 t x3 x4)
                     (Assignment4 f x1 u x3 x4)
                     (f t)
                     (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MyZR

instance Lens.Field3 (Assignment4 f x1 x2 t x4)
                     (Assignment4 f x1 x2 u x4)
                     (f t)
                     (f u) where
  _3 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field4 (Assignment4 f x1 x2 x3 t)
                     (Assignment4 f x1 x2 x3 u)
                     (f t)
                     (f u) where
  _4 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR


------------------------------------------------------------------------
-- 5 field lens combinators

type Assignment5 f x1 x2 x3 x4 x5
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5)

instance Lens.Field1 (Assignment5 f t x2 x3 x4 x5)
                     (Assignment5 f u x2 x3 x4 x5)
                     (f t)
                     (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field2 (Assignment5 f x1 t x3 x4 x5)
                     (Assignment5 f x1 u x3 x4 x5)
                     (f t)
                     (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MyZR

instance Lens.Field3 (Assignment5 f x1 x2 t x4 x5)
                     (Assignment5 f x1 x2 u x4 x5)
                     (f t)
                     (f u) where
  _3 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MyZR

instance Lens.Field4 (Assignment5 f x1 x2 x3 t x5)
                     (Assignment5 f x1 x2 x3 u x5)
                     (f t)
                     (f u) where
  _4 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field5 (Assignment5 f x1 x2 x3 x4 t)
                     (Assignment5 f x1 x2 x3 x4 u)
                     (f t)
                     (f u) where
  _5 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR

------------------------------------------------------------------------
-- 6 field lens combinators

type Assignment6 f x1 x2 x3 x4 x5 x6
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6)

instance Lens.Field1 (Assignment6 f t x2 x3 x4 x5 x6)
                     (Assignment6 f u x2 x3 x4 x5 x6)
                     (f t)
                     (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field2 (Assignment6 f x1 t x3 x4 x5 x6)
                     (Assignment6 f x1 u x3 x4 x5 x6)
                     (f t)
                     (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field3 (Assignment6 f x1 x2 t x4 x5 x6)
                     (Assignment6 f x1 x2 u x4 x5 x6)
                     (f t)
                     (f u) where
  _3 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MyZR

instance Lens.Field4 (Assignment6 f x1 x2 x3 t x5 x6)
                     (Assignment6 f x1 x2 x3 u x5 x6)
                     (f t)
                     (f u) where
  _4 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MyZR

instance Lens.Field5 (Assignment6 f x1 x2 x3 x4 t x6)
                     (Assignment6 f x1 x2 x3 x4 u x6)
                     (f t)
                     (f u) where
  _5 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field6 (Assignment6 f x1 x2 x3 x4 x5 t)
                     (Assignment6 f x1 x2 x3 x4 x5 u)
                     (f t)
                     (f u) where
  _6 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR

------------------------------------------------------------------------
-- 7 field lens combinators

type Assignment7 f x1 x2 x3 x4 x5 x6 x7
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6 '::> x7)

instance Lens.Field1 (Assignment7 f t x2 x3 x4 x5 x6 x7)
                     (Assignment7 f u x2 x3 x4 x5 x6 x7)
                     (f t)
                     (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field2 (Assignment7 f x1 t x3 x4 x5 x6 x7)
                     (Assignment7 f x1 u x3 x4 x5 x6 x7)
                     (f t)
                     (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field3 (Assignment7 f x1 x2 t x4 x5 x6 x7)
                     (Assignment7 f x1 x2 u x4 x5 x6 x7)
                     (f t)
                     (f u) where
  _3 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field4 (Assignment7 f x1 x2 x3 t x5 x6 x7)
                     (Assignment7 f x1 x2 x3 u x5 x6 x7)
                     (f t)
                     (f u) where
  _4 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MyZR

instance Lens.Field5 (Assignment7 f x1 x2 x3 x4 t x6 x7)
                     (Assignment7 f x1 x2 x3 x4 u x6 x7)
                     (f t)
                     (f u) where
  _5 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MyZR

instance Lens.Field6 (Assignment7 f x1 x2 x3 x4 x5 t x7)
                     (Assignment7 f x1 x2 x3 x4 x5 u x7)
                     (f t)
                     (f u) where
  _6 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field7 (Assignment7 f x1 x2 x3 x4 x5 x6 t)
                     (Assignment7 f x1 x2 x3 x4 x5 x6 u)
                     (f t)
                     (f u) where
  _7 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR

------------------------------------------------------------------------
-- 8 field lens combinators

type Assignment8 f x1 x2 x3 x4 x5 x6 x7 x8
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6 '::> x7 '::> x8)

instance Lens.Field1 (Assignment8 f t x2 x3 x4 x5 x6 x7 x8)
                     (Assignment8 f u x2 x3 x4 x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MyZR


instance Lens.Field2 (Assignment8 f x1 t x3 x4 x5 x6 x7 x8)
                     (Assignment8 f x1 u x3 x4 x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field3 (Assignment8 f x1 x2 t x4 x5 x6 x7 x8)
                     (Assignment8 f x1 x2 u x4 x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _3 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field4 (Assignment8 f x1 x2 x3 t x5 x6 x7 x8)
                     (Assignment8 f x1 x2 x3 u x5 x6 x7 x8)
                     (f t)
                     (f u) where
  _4 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field5 (Assignment8 f x1 x2 x3 x4 t x6 x7 x8)
                     (Assignment8 f x1 x2 x3 x4 u x6 x7 x8)
                     (f t)
                     (f u) where
  _5 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MyZR

instance Lens.Field6 (Assignment8 f x1 x2 x3 x4 x5 t x7 x8)
                     (Assignment8 f x1 x2 x3 x4 x5 u x7 x8)
                     (f t)
                     (f u) where
  _6 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MyZR

instance Lens.Field7 (Assignment8 f x1 x2 x3 x4 x5 x6 t x8)
                     (Assignment8 f x1 x2 x3 x4 x5 x6 u x8)
                     (f t)
                     (f u) where
  _7 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field8 (Assignment8 f x1 x2 x3 x4 x5 x6 x7 t)
                     (Assignment8 f x1 x2 x3 x4 x5 x6 x7 u)
                     (f t)
                     (f u) where
  _8 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR

------------------------------------------------------------------------
-- 9 field lens combinators

type Assignment9 f x1 x2 x3 x4 x5 x6 x7 x8 x9
   = Assignment f ('EmptyCtx '::> x1 '::> x2 '::> x3 '::> x4 '::> x5 '::> x6 '::> x7 '::> x8 '::> x9)


instance Lens.Field1 (Assignment9 f t x2 x3 x4 x5 x6 x7 x8 x9)
                     (Assignment9 f u x2 x3 x4 x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _1 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field2 (Assignment9 f x1 t x3 x4 x5 x6 x7 x8 x9)
                     (Assignment9 f x1 u x3 x4 x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _2 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field3 (Assignment9 f x1 x2 t x4 x5 x6 x7 x8 x9)
                     (Assignment9 f x1 x2 u x4 x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _3 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field4 (Assignment9 f x1 x2 x3 t x5 x6 x7 x8 x9)
                     (Assignment9 f x1 x2 x3 u x5 x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _4 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field5 (Assignment9 f x1 x2 x3 x4 t x6 x7 x8 x9)
                     (Assignment9 f x1 x2 x3 x4 u x6 x7 x8 x9)
                     (f t)
                     (f u) where
  _5 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MySR $ MyZR

instance Lens.Field6 (Assignment9 f x1 x2 x3 x4 x5 t x7 x8 x9)
                     (Assignment9 f x1 x2 x3 x4 x5 u x7 x8 x9)
                     (f t)
                     (f u) where
  _6 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MySR $ MyZR

instance Lens.Field7 (Assignment9 f x1 x2 x3 x4 x5 x6 t x8 x9)
                     (Assignment9 f x1 x2 x3 x4 x5 x6 u x8 x9)
                     (f t)
                     (f u) where
  _7 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MySR $ MyZR

instance Lens.Field8 (Assignment9 f x1 x2 x3 x4 x5 x6 x7 t x9)
                     (Assignment9 f x1 x2 x3 x4 x5 x6 x7 u x9)
                     (f t)
                     (f u) where
  _8 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MySR $ MyZR

instance Lens.Field9 (Assignment9 f x1 x2 x3 x4 x5 x6 x7 x8 t)
                     (Assignment9 f x1 x2 x3 x4 x5 x6 x7 x8 u)
                     (f t)
                     (f u) where
  _9 = Lens.lens (mynat_lookup n) (strong_ctx_update n)
        where n = MyZR
