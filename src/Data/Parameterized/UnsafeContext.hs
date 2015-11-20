{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Parameterized.UnsafeContext
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

import Control.Applicative hiding (empty)
import qualified Control.Category as Cat
import Control.DeepSeq
import Control.Exception
import qualified Control.Lens as Lens
import Control.Monad.Identity (Identity(..))
import Data.Bits
import Data.Hashable
import Data.List (intercalate)
import Data.Proxy
import Unsafe.Coerce

import Prelude hiding (init, map, null, replicate, succ, zipWith, (!!))

import Data.Parameterized.Classes
import Data.Parameterized.Ctx
import Data.Parameterized.Some
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

instance Show (Size ctx) where
  show (Size i) = show i

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
nextIndex n = Index (sizeInt n)

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
forIndex n f = go 0
  where go :: Int -> r -> r
        go i v | i < sizeInt n = go (i+1) (f v (Index i))
               | otherwise = v

-- | Return index at given integer or nothing if integer is out of bounds.
intIndex :: Int -> Size ctx -> Maybe (Some (Index ctx))
intIndex i n | 0 <= i && i < sizeInt n = Just (Some (Index i))
             | otherwise = Nothing

instance Show (Index ctx tp) where
   show = show . indexVal

instance ShowF (Index ctx) where
   showF = show

------------------------------------------------------------------------
-- BinTreeKind

data BinTreeKind (x :: *) = PType (BinTreeKind x) (BinTreeKind x)
                          | Elt x

type family Fst (x :: BinTreeKind k) :: BinTreeKind k
type instance Fst ('PType x y) = x

type family Snd (x :: BinTreeKind k) :: BinTreeKind k
type instance Snd ('PType x y) = y

-- | This pairs adjacent elements in a context.
type family PairCtx (x :: Ctx (BinTreeKind k)) :: Ctx (BinTreeKind k)
type instance PairCtx EmptyCtx = EmptyCtx
type instance PairCtx ((x ::> y) ::> z) = PairCtx x ::> 'PType y z

-- | This pairs adjacent elements in a context.
type family UnPairCtx (x :: Ctx (BinTreeKind k)) :: Ctx (BinTreeKind k)
type instance UnPairCtx EmptyCtx = EmptyCtx
type instance UnPairCtx (x ::> 'PType y z) = UnPairCtx x ::> y ::> z

------------------------------------------------------------------------
-- Height

data Height = Zero | Succ Height

type family Pred (k :: Height) :: Height
type instance Pred ('Succ h) = h

------------------------------------------------------------------------
-- BalancedTree

-- | A balanced tree where all leaves are at the same height.
data BalancedTree h f (p :: BinTreeKind k) where
  BalLeaf :: !(f x) -> BalancedTree 'Zero f ('Elt x)
  BalPair :: !(BalancedTree h f x)
          -> !(BalancedTree h f y)
          -> BalancedTree ('Succ h) f ('PType x y)

_bal_height :: BalancedTree h f p -> Int
_bal_height (BalLeaf _) = 0
_bal_height (BalPair x _) = 1 + _bal_height x

bal_size :: BalancedTree h f p -> Int
bal_size (BalLeaf _) = 1
bal_size (BalPair x y) = bal_size x + bal_size y

instance TestEquality f => TestEquality (BalancedTree h f) where
  testEquality (BalLeaf x) (BalLeaf y) = do
    Refl <- testEquality x y
    return Refl
  testEquality (BalPair x1 x2) (BalPair y1 y2) = do
    Refl <- testEquality x1 y1
    Refl <- testEquality x2 y2
    return Refl
  testEquality _ _ = Nothing

instance OrdF f => OrdF (BalancedTree h f) where
  compareF (BalLeaf x) (BalLeaf y) = do
    case compareF x y of
      LTF -> LTF
      GTF -> GTF
      EQF -> EQF
  compareF BalLeaf{} _ = LTF
  compareF _ BalLeaf{} = GTF

  compareF (BalPair x1 x2) (BalPair y1 y2) = do
    case compareF x1 y1 of
      LTF -> LTF
      GTF -> GTF
      EQF ->
        case compareF x2 y2 of
          LTF -> LTF
          GTF -> GTF
          EQF -> EQF

instance HashableF f => HashableF (BalancedTree h f) where
  hashWithSaltF s t =
    case t of
      BalLeaf x -> s `hashWithSaltF` x
      BalPair x y -> s `hashWithSaltF` x `hashWithSaltF` y

fmap_bal ::(forall tp . f tp -> g tp)
             -> BalancedTree h f c
             -> BalancedTree h g c
fmap_bal = go
  where go :: (forall tp . f tp -> g tp)
              -> BalancedTree h f c
              -> BalancedTree h g c
        go f (BalLeaf x) = BalLeaf (f x)
        go f (BalPair x y) = BalPair (go f x) (go f y)
{-# INLINABLE fmap_bal #-}

traverse_bal :: Applicative m
             => (forall tp . f tp -> m (g tp))
             -> BalancedTree h f c
             -> m (BalancedTree h g c)
traverse_bal = go
  where go :: Applicative m
              => (forall tp . f tp -> m (g tp))
              -> BalancedTree h f c
              -> m (BalancedTree h g c)
        go f (BalLeaf x) = BalLeaf <$> f x
        go f (BalPair x y) = BalPair <$> go f x <*> go f y
{-# INLINABLE traverse_bal #-}

instance ShowF f => ShowF (BalancedTree h f) where
  showF (BalLeaf x) = showF x
  showF (BalPair x y) = "BalPair " ++ showF x ++ " " ++ showF y

unsafe_bal_generate :: forall ctx h f t
                     . Int -- ^ Height of tree to generate
                    -> Int -- ^ Starting offset for entries.
                    -> (forall tp . Index ctx tp -> f tp)
                    -> BalancedTree h f t
unsafe_bal_generate h o f
  | h <  0 = error "unsafe_bal_generate given negative height"
  | h == 0 = unsafeCoerce $ BalLeaf (f (Index o))
  | otherwise =
    let l = unsafe_bal_generate (h-1) o f
        o' = o + 1 `shiftL` (h-1)
        u = assert (o + bal_size l == o') $ unsafe_bal_generate (h-1) o' f
        r :: BalancedTree ('Succ (Pred h)) f ('PType (Fst t) (Snd t))
        r = BalPair l u
     in unsafeCoerce r

unsafe_bal_generateM :: forall m ctx h f t
                      . Applicative m
                     => Int -- ^ Height of tree to generate
                     -> Int -- ^ Starting offset for entries.
                     -> (forall x . Index ctx x -> m (f x))
                     -> m (BalancedTree h f t)
unsafe_bal_generateM h o f
  | h == 0 = fmap unsafeCoerce $ BalLeaf <$> f (Index o)
  | otherwise =
    let l = unsafe_bal_generateM (h-1) o f
        o' = o + 1 `shiftL` (h-1)
        u = unsafe_bal_generateM (h-1) o' f
        r :: m (BalancedTree ('Succ (Pred h)) f ('PType (Fst t) (Snd t)))
        r = (\lv uv -> assert (o' == o + bal_size lv) $ BalPair lv uv) <$> l <*> u
      in fmap unsafeCoerce r

-- | Lookup index in tree.
_bal_index :: BalancedTree h f a -- ^ Tree to lookup.
           -> Int -- ^ Index to lookup.
           -> Int  -- ^ Height of tree
           -> Some f
_bal_index (BalLeaf u) _ i = assert (i == 0) $ Some u
_bal_index (BalPair x y) j i
  | j `testBit` (i-1) = _bal_index y j (i-1)
  | otherwise         = _bal_index x j (i-1)

-- | Lookup index in tree.
unsafe_bal_index :: BalancedTree h f a -- ^ Tree to lookup.
                 -> Int -- ^ Index to lookup.
                 -> Int  -- ^ Height of tree
                 -> f tp
unsafe_bal_index _ j i
  | seq j $ seq i $ False = error "bad unsafe_bal_index"
unsafe_bal_index (BalLeaf u) _ i = assert (i == 0) $ unsafeCoerce u
unsafe_bal_index (BalPair x y) j i
  | j `testBit` (i-1) = unsafe_bal_index y j $! (i-1)
  | otherwise         = unsafe_bal_index x j $! (i-1)

-- | Update value at index in tree.
unsafe_bal_adjust :: (f x -> f y)
                  -> BalancedTree h f a -- ^ Tree to update
                  -> Int -- ^ Index to lookup.
                  -> Int  -- ^ Height of tree
                  -> BalancedTree h f b
unsafe_bal_adjust f (BalLeaf u) _ i = assert (i == 0) $
  unsafeCoerce (BalLeaf (f (unsafeCoerce u)))
unsafe_bal_adjust f (BalPair x y) j i
  | j `testBit` (i-1) = unsafeCoerce $ BalPair x (unsafe_bal_adjust f y j (i-1))
  | otherwise         = unsafeCoerce $ BalPair (unsafe_bal_adjust f x j (i-1)) y

-- | Zip two balanced trees together.
bal_zipWithM :: Applicative m
             => (forall x . f x -> g x -> m (h x))
             -> BalancedTree u f a
             -> BalancedTree u g a
             -> m (BalancedTree u h a)
bal_zipWithM f (BalLeaf x) (BalLeaf y) = BalLeaf <$> f x y
bal_zipWithM f (BalPair x1 x2) (BalPair y1 y2) =
  BalPair <$> bal_zipWithM f x1 y1 <*> bal_zipWithM f x2 y2
bal_zipWithM _ _ _ = error "ilegal args to bal_zipWithM"
{-# INLINABLE bal_zipWithM #-}

------------------------------------------------------------------------
-- BinomialTree

data BinomialTree (h::Height) (f :: k -> *) :: Ctx (BinTreeKind k) -> * where
  Empty :: BinomialTree h f EmptyCtx

  -- Contains size of the subtree, subtree, then element.
  PlusOne  :: (x ~ PairCtx z)
           => !Int
           -> !(BinomialTree ('Succ h) f x)
           -> !(BalancedTree h f y)
           -> BinomialTree h f (z ::> y)

  -- Contains size of the subtree, subtree, then element.
  PlusZero  :: (x ~ PairCtx z)
            => !Int
            -> !(BinomialTree ('Succ h) f x)
            -> BinomialTree h f z


tsize :: BinomialTree h f a -> Int
tsize Empty = 0
tsize (PlusOne s _ _) = 2*s+1
tsize (PlusZero  s _) = 2*s

t_cnt_size :: BinomialTree h f a -> Int
t_cnt_size Empty = 0
t_cnt_size (PlusOne _ l r) = t_cnt_size l + bal_size r
t_cnt_size (PlusZero  _ l) = t_cnt_size l

append :: BinomialTree h f x
       -> BalancedTree h f (y :: BinTreeKind k)
       -> BinomialTree h f (x ::> y)
append Empty y = PlusOne 0 Empty y
append (PlusOne _ t x) y = PlusZero (tsize t') t'
  where t' = append t (BalPair x y)
append (PlusZero s t) x = PlusOne s t x

instance TestEquality f => TestEquality (BinomialTree h f) where
  testEquality Empty Empty = return Refl
  testEquality (PlusZero _ x1) (PlusZero _ y1) = do
    Refl <- testEquality x1 y1
    return (unsafeCoerce Refl)
  testEquality (PlusOne _ x1 x2) (PlusOne _ y1 y2) = do
    Refl <- testEquality x1 y1
    Refl <- testEquality x2 y2
    return (unsafeCoerce Refl)
  testEquality _ _ = Nothing

instance OrdF f => OrdF (BinomialTree h f) where
  compareF Empty Empty = EQF
  compareF Empty _ = LTF
  compareF _ Empty = GTF

  compareF (PlusZero _ x1) (PlusZero _ y1) = do
    case compareF x1 y1 of
      LTF -> LTF
      GTF -> GTF
      EQF -> unsafeCoerce EQF
  compareF PlusZero{} _ = LTF
  compareF _ PlusZero{} = GTF

  compareF (PlusOne _ x1 x2) (PlusOne _ y1 y2) = do
    case compareF x1 y1 of
      LTF -> LTF
      GTF -> GTF
      EQF ->
        case compareF x2 y2 of
          LTF -> LTF
          GTF -> GTF
          EQF -> unsafeCoerce EQF

instance HashableF f => HashableF (BinomialTree h f) where
  hashWithSaltF s t =
    case t of
      Empty -> s
      PlusZero _ x   -> s `hashWithSaltF` x
      PlusOne  _ x y -> s `hashWithSaltF` x `hashWithSaltF` y

fmap_bin :: (forall tp . f tp -> g tp)
            -> BinomialTree h f c
            -> BinomialTree h g c
fmap_bin = go
  where go :: (forall tp . f tp -> g tp)
              -> BinomialTree h f c
              -> BinomialTree h g c
        go _ Empty = Empty
        go f (PlusOne s t x) = PlusOne s  (fmap_bin f t) (fmap_bal f x)
        go f (PlusZero s t)  = PlusZero s (fmap_bin f t)
{-# INLINABLE fmap_bin #-}

traverse_bin :: Applicative m
             => (forall tp . f tp -> m (g tp))
             -> BinomialTree h f c
             -> m (BinomialTree h g c)
traverse_bin = go
  where go :: Applicative m
              => (forall tp . f tp -> m (g tp))
              -> BinomialTree h f c
              -> m (BinomialTree h g c)
        go _ Empty = pure Empty
        go f (PlusOne s t x) = PlusOne s  <$> traverse_bin f t <*> traverse_bal f x
        go f (PlusZero s t)  = PlusZero s <$> traverse_bin f t
{-# INLINABLE traverse_bin #-}

unsafe_bin_generate :: forall h f ctx t
                     . Int -- ^ Size of tree to generate
                    -> Int -- ^ Height of each element.
                    -> (forall x . Index ctx x -> f x)
                    -> BinomialTree h f t
unsafe_bin_generate sz h f
  | sz == 0 = unsafeCoerce Empty
  | sz `testBit` 0 =
    let s = sz `shiftR` 1
        t = unsafe_bin_generate s (h+1) f
        o = s * 2^(h+1)
        u = assert (o == t_cnt_size t) $ unsafe_bal_generate h o f
        r :: BinomialTree h f (InitCtx t ::> LastCtx t)
        r = PlusOne s t u
     in unsafeCoerce r
  | otherwise =
    let s = sz `shiftR` 1
        t = unsafe_bin_generate (sz `shiftR` 1) (h+1) f
        r :: BinomialTree h f t
        r = PlusZero s t
     in r

unsafe_bin_generateM :: forall m h f ctx t
                      . Applicative m
                     => Int -- ^ Size of tree to generate
                     -> Int -- ^ Height of each element.
                     -> (forall x . Index ctx x -> m (f x))
                     -> m (BinomialTree h f t)
unsafe_bin_generateM sz h f
  | sz == 0 = pure (unsafeCoerce Empty)
  | sz `testBit` 0 =
    let s = sz `shiftR` 1
        t = unsafe_bin_generateM s (h+1) f
        -- Next offset
        o = s * 2^(h+1)
        u = unsafe_bal_generateM h o f
        r :: m (BinomialTree h f (InitCtx t ::> LastCtx t))
        r = PlusOne s <$> t <*> u
     in fmap unsafeCoerce r
  | otherwise =
    let s = sz `shiftR` 1
        t = unsafe_bin_generateM s (h+1) f
        r :: m (BinomialTree h f t)
        r = PlusZero s <$> t
     in r

type family Flatten1 (x :: Ctx (BinTreeKind k)) :: Ctx (BinTreeKind k)
type instance Flatten1 EmptyCtx = EmptyCtx

type family Flatten (h :: Height) (x :: Ctx (BinTreeKind k)) :: Ctx (BinTreeKind k)
type instance Flatten 'Zero     x = x
type instance Flatten ('Succ h) x = Flatten h (Flatten1 x)

type family Append (x :: Ctx k) (y :: Ctx k) :: Ctx k
type instance Append x EmptyCtx = x
type instance Append x (y ::> z) = Append x y ::> z


type family FlattenBin (x :: BinTreeKind k) :: Ctx (BinTreeKind k)
type instance FlattenBin ('Elt x) = EmptyCtx ::> 'Elt x
type instance FlattenBin ('PType x y) = Append (FlattenBin x) (FlattenBin y)

-- | Drop last element from binary and flatten it.
type family DropBin (x :: BinTreeKind k) :: Ctx (BinTreeKind k)
type instance DropBin ('Elt x) = EmptyCtx
type instance DropBin ('PType x y) = Append (FlattenBin x) (DropBin y)

type family InitCtx (x :: Ctx k) :: Ctx k
type instance InitCtx (x ::> y) = x

type family LastCtx (x :: Ctx k) :: k
type instance LastCtx (x ::> y) = y

data DropResult f (ctx :: Ctx (BinTreeKind k)) where
  DropEmpty :: DropResult f EmptyCtx
  DropExt   :: BinomialTree 'Zero f (InitCtx ctx)
            -> f (LastCtx (UnElt ctx))
            -> DropResult f ctx

bal_drop :: forall h f x y
          . BinomialTree h f x
         -> BalancedTree h f y
         -> DropResult f (Append x (FlattenBin y))
bal_drop t (BalLeaf e) = DropExt t e
bal_drop t (BalPair x y) =
  let m :: BinomialTree h f (PairCtx (UnPairCtx x))
      m = unsafeCoerce t

      n :: ('Succ g ~ h) => BinomialTree g f (UnPairCtx x ::> Fst y)
      n = PlusOne (tsize t) m x

      a :: DropResult f (Append (UnPairCtx x ::> Fst y) (FlattenBin (Snd y)))
      a = bal_drop n y

      w :: DropResult f (Append x (FlattenBin y))
      w = unsafeCoerce a

   in w

bin_drop :: forall h f ctx
          . BinomialTree h f ctx
         -> DropResult f (Flatten h ctx)
bin_drop Empty = unsafeCoerce DropEmpty
bin_drop (PlusZero _ u) =
  let v :: DropResult f (Flatten h (Flatten1 (PairCtx ctx)))
      v = bin_drop u
   in unsafeCoerce v
bin_drop (PlusOne s t u) =
  let m :: BinomialTree h f (InitCtx ctx)
      m = case t of
            Empty -> unsafeCoerce Empty
            _ -> PlusZero s t
      q :: DropResult f (Append (InitCtx ctx) (FlattenBin (LastCtx ctx)))
      q = bal_drop m u
   in unsafeCoerce q

-- | Lookup value in tree.
_bin_index :: BinomialTree h f a -- ^ Tree to lookup in.
           -> Int
           -> Int -- ^ Size of tree
           -> Some f
_bin_index Empty _ _ = error "bin_index reached end of list"
_bin_index (PlusOne sz t u) j i
   | sz == j `shiftR` (1+i) = _bal_index u j i
   | otherwise = _bin_index t j (1+i)
_bin_index (PlusZero sz t) j i
  | sz == j `shiftR` (1+i) = error "bin_index stopped at PlusZero"
  | otherwise = _bin_index t j (1+i)

-- | Lookup value in tree.
unsafe_bin_index :: BinomialTree h f a -- ^ Tree to lookup in.
                 -> Int
                 -> Int -- ^ Size of tree
                 -> f u
unsafe_bin_index _ _ i
  | seq i False = error "bad unsafe_bin_index"
unsafe_bin_index Empty _ _ = error "unsafe_bin_index reached end of list"
unsafe_bin_index (PlusOne sz t u) j i
  | sz == j `shiftR` (1+i) = unsafe_bal_index u j i
  | otherwise = unsafe_bin_index t j $! (1+i)
unsafe_bin_index (PlusZero sz t) j i
  | sz == j `shiftR` (1+i) = error "unsafe_bin_index stopped at PlusZero"
  | otherwise = unsafe_bin_index t j $! (1+i)

-- | Lookup value in tree.
unsafe_bin_adjust :: forall h f x y a b
                   . (f x -> f y)
                  -> BinomialTree h f a -- ^ Tree to lookup in.
                  -> Int
                  -> Int -- ^ Size of tree
                  -> BinomialTree h f b
unsafe_bin_adjust _ Empty _ _ = error "unsafe_bin_adjust reached end of list"
unsafe_bin_adjust f (PlusOne sz t u) j i
  | sz == j `shiftR` (1+i) = do
    let t' :: BinomialTree ('Succ h) f (PairCtx (InitCtx b))
        t' = unsafeCoerce t
        u' :: BalancedTree h f (LastCtx b)
        u' = unsafe_bal_adjust f u j i
        r :: BinomialTree h f (InitCtx b ::> LastCtx b)
        r = PlusOne sz t' u'
     in unsafeCoerce r
  | otherwise =
    let t' :: BinomialTree ('Succ h) f (PairCtx (InitCtx b))
        t' = unsafe_bin_adjust f t j (i+1)
        u' :: BalancedTree h f (LastCtx b)
        u' = unsafeCoerce u
        r  :: BinomialTree h f (InitCtx b ::> LastCtx b)
        r  = PlusOne sz t' u'
     in unsafeCoerce r
unsafe_bin_adjust f (PlusZero sz t) j i
  | sz == j `shiftR` (1+i) = error "unsafe_bin_adjust stopped at PlusZero"
  | otherwise =
    let t' :: BinomialTree ('Succ h) f (PairCtx b)
        t' = unsafe_bin_adjust f t j (i+1)
        r  :: BinomialTree h f b
        r  = PlusZero sz t'
     in r
{-# NOINLINE unsafe_bin_adjust #-}

tree_zipWithM :: Applicative m
             => (forall x . f x -> g x -> m (h x))
             -> BinomialTree u f a
             -> BinomialTree u g a
             -> m (BinomialTree u h a)
tree_zipWithM _ Empty Empty = pure Empty
tree_zipWithM f (PlusOne s x1 x2) (PlusOne _ y1 y2) =
  PlusOne s <$> tree_zipWithM f x1 y1
            <*> bal_zipWithM  f x2 y2
tree_zipWithM f (PlusZero s x1) (PlusZero _ y1) =
  PlusZero s <$> tree_zipWithM f x1 y1
tree_zipWithM _ _ _ = error "ilegal args to tree_zipWithM"
{-# INLINABLE tree_zipWithM #-}

------------------------------------------------------------------------
-- Assignment

type family UnElt (x :: Ctx (BinTreeKind k)) :: Ctx k
type instance UnElt EmptyCtx = EmptyCtx
type instance UnElt (c ::> 'Elt y) = UnElt c ::> y

type family UnFlatten (x :: Ctx k) :: Ctx (BinTreeKind k)
type instance UnFlatten EmptyCtx = EmptyCtx
type instance UnFlatten (c ::> y) = UnFlatten c ::> 'Elt y

type role Assignment representational nominal

newtype Assignment (f :: k -> *) (ctx :: Ctx k)
      = Assignment (BinomialTree 'Zero f (UnFlatten ctx))

instance NFData (Assignment f ctx) where
  rnf a = seq a ()

-- | Return number of elements in assignment.
size :: Assignment f ctx -> Size ctx
size (Assignment t) = Size (tsize t)

-- | @replicate n@ make a context with different copies of the same
-- polymorphic value.
replicate :: Size ctx -> (forall tp . f tp) -> Assignment f ctx
replicate n c = generate n (\_ -> c)

-- | Generate an assignment
generate :: Size ctx
         -> (forall tp . Index ctx tp -> f tp)
         -> Assignment f ctx
generate n f  = Assignment r
  where r = unsafe_bin_generate (sizeInt n) 0 f
{-# NOINLINE generate #-}

-- | Generate an assignment
generateM :: Applicative m
          => Size ctx
          -> (forall tp . Index ctx tp -> m (f tp))
          -> m (Assignment f ctx)
generateM n f = Assignment <$> unsafe_bin_generateM (sizeInt n) 0 f
{-# NOINLINE generateM #-}

-- | Return empty assignment
empty :: Assignment f EmptyCtx
empty = Assignment Empty

-- | Return true if assignment is empty.
null :: Assignment f ctx -> Bool
null (Assignment Empty) = True
null (Assignment _) = False

extend :: Assignment f ctx -> f x -> Assignment f (ctx ::> x)
extend (Assignment x) y = Assignment $ append x (BalLeaf y)

(%>) :: Assignment f x -> f tp -> Assignment f (x ::> tp)
a %> v = extend a v

-- | Unexported index that returns an arbitrary type of expression.
unsafeIndex :: proxy u -> Int -> Assignment f ctx -> f u
unsafeIndex _ idx (Assignment t) = seq t $ unsafe_bin_index t idx 0

-- | Return value of assignment.
(!) :: Assignment f ctx -> Index ctx tp -> f tp
a ! Index i = assert (0 <= i && i < sizeInt (size a)) $
              unsafeIndex Proxy i a

-- | Return value of assignment.
(!!) :: KnownDiff l r => Assignment f r -> Index l tp -> f tp
a !! i = a ! extendIndex i

instance TestEquality f => Eq (Assignment f ctx) where
  x == y = isJust (testEquality x y)

instance TestEquality f => TestEquality (Assignment f) where
   testEquality (Assignment x) (Assignment y) = do
     Refl <- testEquality x y
     return (unsafeCoerce Refl)

instance OrdF f => OrdF (Assignment f) where
  compareF (Assignment x) (Assignment y) = do
    case compareF x y of
      LTF -> LTF
      GTF -> GTF
      EQF -> unsafeCoerce EQF

instance OrdF f => Ord (Assignment f ctx) where
  compare x y = toOrdering (compareF x y)

instance Hashable (Index ctx tp) where
  hashWithSalt = hashWithSaltF
instance HashableF (Index ctx) where
  hashWithSaltF s i = hashWithSalt s (indexVal i)

instance HashableF f => HashableF (Assignment f) where
  hashWithSaltF = hashWithSalt

instance HashableF f => Hashable (Assignment f ctx) where
  hashWithSalt s (Assignment a) = hashWithSaltF s a

instance ShowF f => ShowF (Assignment f) where
  showF a = "[" ++ intercalate ", " (toList showF a) ++ "]"

instance ShowF f => Show (Assignment f ctx) where
  show a = showF a

-- | Modify the value of an assignment at a particular index.
adjust :: (f tp -> f tp) -> Index ctx tp -> Assignment f ctx -> Assignment f ctx
adjust f (Index i) (Assignment a) = Assignment (unsafe_bin_adjust f a i 0)

-- | Update the assignment at a particular index.
update :: Index ctx tp -> f tp -> Assignment f ctx -> Assignment f ctx
update i v a = adjust (\_ -> v) i a

-- This is an unsafe version of update that changes the type of the expression.
unsafeUpdate :: Int -> Assignment f ctx -> f u -> Assignment f ctx'
unsafeUpdate i (Assignment a) e = Assignment (unsafe_bin_adjust (\_ -> e) a i 0)

data AssignView f ctx where
  AssignEmpty :: AssignView f EmptyCtx
  AssignExtend :: Assignment f ctx
               -> f tp
               -> AssignView f (ctx::>tp)

-- | Return assignment with all but the last block.
view :: forall f ctx . Assignment f ctx -> AssignView f ctx
view (Assignment x) =
  case bin_drop x of
    DropEmpty -> unsafeCoerce AssignEmpty
    DropExt t v -> do
      let t' :: BinomialTree 'Zero f (InitCtx (UnFlatten ctx))
          t' = t
          t2 :: BinomialTree 'Zero f (UnFlatten (InitCtx (UnElt (UnFlatten ctx))))
          t2 = unsafeCoerce t'
          u :: Assignment f (InitCtx (UnElt (UnFlatten ctx)))
          u = Assignment t2
          r :: AssignView f (InitCtx (UnElt (UnFlatten ctx)) ::> LastCtx (UnElt (UnFlatten ctx)))
          r = AssignExtend u v
       in unsafeCoerce r

-- | Return assignment with all but the last block.
init :: Assignment f (ctx '::> tp) -> Assignment f ctx
init (Assignment x) =
  case bin_drop x of
    DropExt t _ -> Assignment t
    _ -> error "init given bad context"

-- | Convert assignment to list.
toList :: (forall tp . f tp -> a) -> Assignment f c -> [a]
toList = toListFC
{-# DEPRECATED toList "Use toListFC" #-}

zipWith :: (forall x . f x -> g x -> h x)
        -> Assignment f a
        -> Assignment g a
        -> Assignment h a
zipWith f = \x y -> runIdentity $ zipWithM (\u v -> pure (f u v)) x y
{-# INLINE zipWith #-}

zipWithM :: Applicative m
         => (forall x . f x -> g x -> m (h x))
         -> Assignment f a
         -> Assignment g a
         -> m (Assignment h a)
zipWithM f (Assignment x) (Assignment y) = Assignment <$> tree_zipWithM f x y
{-# INLINABLE zipWithM #-}

instance FunctorFC Assignment where
  fmapFC = \f (Assignment x) -> Assignment (fmap_bin f x)
  {-# INLINE fmapFC #-}

instance FoldableFC Assignment where
  foldMapFC = foldMapFCDefault
  {-# INLINE foldMapFC #-}

instance TraversableFC Assignment where
  traverseFC = \f (Assignment x) -> Assignment <$> traverse_bin f x
  {-# INLINE traverseFC #-}

traverseWithIndex :: Applicative m
                  => (forall tp . Index ctx tp -> f tp -> m (g tp))
                  -> Assignment f ctx
                  -> m (Assignment g ctx)
traverseWithIndex f a = generateM (size a) $ \i -> f i (a ! i)

------------------------------------------------------------------------
-- Lens combinators

unsafeLens :: Int -> Lens.Lens (Assignment f ctx) (Assignment f ctx') (f tp) (f u)
unsafeLens idx =
  Lens.lens (unsafeIndex Proxy idx) (unsafeUpdate idx)

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
