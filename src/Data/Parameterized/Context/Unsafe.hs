{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyDataDecls #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Parameterized.Context.Unsafe
  ( module Data.Parameterized.Ctx
  , KnownContext(..)
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
    -- * Diff
  , Diff
  , noDiff
  , extendRight
  , DiffView(..)
  , viewDiff
  , KnownDiff(..)
    -- * Indexing
  , Index
  , indexVal
  , baseIndex
  , skipIndex
  , lastIndex
  , nextIndex
  , extendIndex
  , extendIndex'
  , forIndex
  , forIndexRange
  , intIndex
    -- ** IndexRange
  , IndexRange
  , allRange
  , indexOfRange
  , dropHeadRange
  , dropTailRange
    -- * Assignments
  , Assignment
  , size
  , Data.Parameterized.Context.Unsafe.replicate
  , generate
  , generateM
  , empty
  , extend
  , adjustM
  , AssignView(..)
  , viewAssign
  , (!)
  , (!^)
  , Data.Parameterized.Context.Unsafe.zipWith
  , zipWithM
  , (<++>)
  , traverseWithIndex
  ) where

import qualified Control.Category as Cat
import           Control.DeepSeq
import           Control.Exception
import qualified Control.Lens as Lens
import           Control.Monad.Identity (Identity(..))
import           Data.Bits
import           Data.Coerce
import           Data.Hashable
import           Data.List (intercalate)
import           Data.Proxy
import           Unsafe.Coerce

import           Data.Parameterized.Classes
import           Data.Parameterized.Ctx
import           Data.Parameterized.Ctx.Proofs
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

------------------------------------------------------------------------
-- Size

-- | Represents the size of a context.
newtype Size (ctx :: Ctx k) = Size { sizeInt :: Int }

type role Size nominal

-- | The size of an empty context.
zeroSize :: Size 'EmptyCtx
zeroSize = Size 0

-- | Increment the size to the next value.
incSize :: Size ctx -> Size (ctx '::> tp)
incSize (Size n) = Size (n+1)

decSize :: Size (ctx '::> tp) -> Size ctx
decSize (Size n) = assert (n > 0) (Size (n-1))

-- | Allows interpreting a size.
data SizeView (ctx :: Ctx k) where
  ZeroSize :: SizeView 'EmptyCtx
  IncSize :: !(Size ctx) -> SizeView (ctx '::> tp)

-- | Project a size
viewSize :: Size ctx -> SizeView ctx
viewSize (Size 0) = unsafeCoerce ZeroSize
viewSize (Size n) = assert (n > 0) (unsafeCoerce (IncSize (Size (n-1))))

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

-- | The total size of two concatenated contexts.
addSize :: Size x -> Size y -> Size (x <+> y)
addSize (Size x) (Size y) = Size (x + y)


data DiffView a b where
  NoDiff :: DiffView a a
  ExtendRightDiff :: Diff a b -> DiffView a (b ::> r)

viewDiff :: Diff a b -> DiffView a b
viewDiff (Diff i)
  | i == 0 = unsafeCoerce NoDiff
  | otherwise  = assert (i > 0) $ unsafeCoerce $ ExtendRightDiff (Diff (i-1))

------------------------------------------------------------------------
-- KnownDiff

-- | A difference that can be automatically inferred at compile time.
class KnownDiff (l :: Ctx k) (r :: Ctx k) where
  knownDiff :: Diff l r

instance KnownDiff l l where
  knownDiff = noDiff

instance {-# INCOHERENT #-} KnownDiff l r => KnownDiff l (r '::> tp) where
  knownDiff = extendRight knownDiff

------------------------------------------------------------------------
-- Index

-- | An index is a reference to a position with a particular type in a
-- context.
newtype Index (ctx :: Ctx k) (tp :: k) = Index { indexVal :: Int }

type role Index nominal nominal

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
baseIndex :: Index ('EmptyCtx '::> tp) tp
baseIndex = Index 0

-- | Increase context while staying at same index.
skipIndex :: Index ctx x -> Index (ctx '::> y) x
skipIndex (Index i) = Index i

-- | Return the index of a element one past the size.
nextIndex :: Size ctx -> Index (ctx ::> tp) tp
nextIndex n = Index (sizeInt n)

-- | Return the last index of a element.
lastIndex :: Size (ctx ::> tp) -> Index (ctx ::> tp) tp
lastIndex n = Index (sizeInt n - 1)

{-# INLINE extendIndex #-}
extendIndex :: KnownDiff l r => Index l tp -> Index r tp
extendIndex = extendIndex' knownDiff

{-# INLINE extendIndex' #-}
extendIndex' :: Diff l r -> Index l tp -> Index r tp
extendIndex' _ = unsafeCoerce

-- | Given a size 'n', an initial value 'v0', and a function 'f', 'forIndex n v0 f'
-- is equivalent to 'v0' when 'n' is zero, and 'f (forIndex (n-1) v0) (n-1)' otherwise.
forIndex :: forall ctx r
          . Size ctx
         -> (forall tp . r -> Index ctx tp -> r)
         -> r
         -> r
forIndex n f r =
  case viewSize n of
    ZeroSize -> r
    IncSize p -> f (forIndex p (coerce f) r) (nextIndex p)

-- | Given an index 'i', size 'n', a function 'f', value 'v', and a function 'f',
-- 'forIndex i n f v' is equivalent to 'v' when 'i >= sizeInt n', and
-- 'f i (forIndexRange (i+1) n v0)' otherwise.
forIndexRange :: forall ctx r
               . Int
              -> Size ctx
              -> (forall tp . Index ctx tp -> r -> r)
              -> r
              -> r
forIndexRange i (Size n) f r
  | i >= n = r
  | otherwise = f (Index i) (forIndexRange (i+1) (Size n) f r)

-- | Return index at given integer or nothing if integer is out of bounds.
intIndex :: Int -> Size ctx -> Maybe (Some (Index ctx))
intIndex i n | 0 <= i && i < sizeInt n = Just (Some (Index i))
             | otherwise = Nothing

instance Show (Index ctx tp) where
   show = show . indexVal

instance ShowF (Index ctx)

------------------------------------------------------------------------
-- IndexRange

-- | This represents a contiguous range of indices.
data IndexRange (ctx :: Ctx k) (sub :: Ctx k)
   = IndexRange {-# UNPACK #-} !Int
                {-# UNPACK #-} !Int

-- | Return a range containing all indices in the context.
allRange :: Size ctx -> IndexRange ctx ctx
allRange (Size n) = IndexRange 0 n

-- | `indexOfRange` returns the only index in a range.
indexOfRange :: IndexRange ctx (EmptyCtx ::> e) -> Index ctx e
indexOfRange (IndexRange i n) = assert (n == 1) $ Index i

-- | `dropTailRange r n` drops the last `n` elements in `r`.
dropTailRange :: IndexRange ctx (x <+> y) -> Size y -> IndexRange ctx x
dropTailRange (IndexRange i n) (Size j) = assert (n >= j) $ IndexRange i (n - j)

-- | `dropHeadRange r n` drops the first `n` elements in `r`.
dropHeadRange :: IndexRange ctx (x <+> y) -> Size x -> IndexRange ctx y
dropHeadRange (IndexRange i n) (Size j) = assert (i' >= i && n >= j) $ IndexRange i' (n - j)
  where i' = i + j

------------------------------------------------------------------------
-- Height

data Height = Zero | Succ Height

type family Pred (k :: Height) :: Height
type instance Pred ('Succ h) = h

------------------------------------------------------------------------
-- BalancedTree

-- | A balanced tree where all leaves are at the same height.
--
-- The first parameter is the height of the tree.
-- The second is the parameterized value.
data BalancedTree h (f :: k -> *) (p :: Ctx k) where
  BalLeaf :: !(f x) -> BalancedTree 'Zero f (SingleCtx x)
  BalPair :: !(BalancedTree h f x)
          -> !(BalancedTree h f y)
          -> BalancedTree ('Succ h) f (x <+> y)

bal_size :: BalancedTree h f p -> Int
bal_size (BalLeaf _) = 1
bal_size (BalPair x y) = bal_size x + bal_size y


instance TestEqualityFC (BalancedTree h) where
  testEqualityFC test (BalLeaf x) (BalLeaf y) = do
    Refl <- test x y
    return Refl
  testEqualityFC test (BalPair x1 x2) (BalPair y1 y2) = do
    Refl <- testEqualityFC test x1 y1
    Refl <- testEqualityFC test x2 y2
    return Refl
#if !MIN_VERSION_base(4,9,0)
  testEqualityFC _ _ _ = Nothing
#endif

instance OrdFC (BalancedTree h) where
  compareFC test (BalLeaf x) (BalLeaf y) =
    joinOrderingF (test x y) $ EQF
#if !MIN_VERSION_base(4,9,0)
  compareFC _ BalLeaf{} _ = LTF
  compareFC _ _ BalLeaf{} = GTF
#endif
  compareFC test (BalPair x1 x2) (BalPair y1 y2) =
    joinOrderingF (compareFC test x1 y1) $
    joinOrderingF (compareFC test x2 y2) $
    EQF

instance HashableF f => HashableF (BalancedTree h f) where
  hashWithSaltF s t =
    case t of
      BalLeaf x -> s `hashWithSaltF` x
      BalPair x y -> s `hashWithSaltF` x `hashWithSaltF` y

fmap_bal :: (forall tp . f tp -> g tp)
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

instance ShowF f => Show (BalancedTree h f tp) where
  show (BalLeaf x) = showF x
  show (BalPair x y) = "BalPair " Prelude.++ show x Prelude.++ " " Prelude.++ show y

instance ShowF f => ShowF (BalancedTree h f)

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
     in unsafeCoerce $ BalPair l u

unsafe_bal_generateM :: forall m ctx h f t
                      . Applicative m
                     => Int -- ^ Height of tree to generate
                     -> Int -- ^ Starting offset for entries.
                     -> (forall x . Index ctx x -> m (f x))
                     -> m (BalancedTree h f t)
unsafe_bal_generateM h o f
  | h == 0 = unsafeCoerce . BalLeaf <$> f (Index o)
  | otherwise =
    let o' = o + 1 `shiftL` (h-1)
        g lv uv = assert (o' == o + bal_size lv) $
           unsafeCoerce (BalPair lv uv)
      in g <$> unsafe_bal_generateM (h-1) o  f
           <*> unsafe_bal_generateM (h-1) o' f

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
unsafe_bal_adjust :: Functor m
                  => (f x -> m (f y))
                  -> BalancedTree h f a -- ^ Tree to update
                  -> Int -- ^ Index to lookup.
                  -> Int  -- ^ Height of tree
                  -> m (BalancedTree h f b)
unsafe_bal_adjust f (BalLeaf u) _ i = assert (i == 0) $
  (unsafeCoerce . BalLeaf <$> (f (unsafeCoerce u)))
unsafe_bal_adjust f (BalPair x y) j i
  | j `testBit` (i-1) = (unsafeCoerce . BalPair x      <$> (unsafe_bal_adjust f y j (i-1)))
  | otherwise         = (unsafeCoerce . flip BalPair y <$> (unsafe_bal_adjust f x j (i-1)))

{-# SPECIALIZE unsafe_bal_adjust
     :: (f x -> Identity (f y))
     -> BalancedTree h f a
     -> Int
     -> Int
     -> Identity (BalancedTree h f b)
  #-}

-- | Zip two balanced trees together.
bal_zipWithM :: Applicative m
             => (forall x . f x -> g x -> m (h x))
             -> BalancedTree u f a
             -> BalancedTree u g a
             -> m (BalancedTree u h a)
bal_zipWithM f (BalLeaf x) (BalLeaf y) = BalLeaf <$> f x y
bal_zipWithM f (BalPair x1 x2) (BalPair y1 y2) =
  BalPair <$> bal_zipWithM f x1 (unsafeCoerce y1)
          <*> bal_zipWithM f x2 (unsafeCoerce y2)
#if !MIN_VERSION_base(4,9,0)
bal_zipWithM _ _ _ = error "ilegal args to bal_zipWithM"
#endif
{-# INLINABLE bal_zipWithM #-}

------------------------------------------------------------------------
-- BinomialTree

data BinomialTree (h::Height) (f :: k -> *) :: Ctx k -> * where
  Empty :: BinomialTree h f EmptyCtx

  -- Contains size of the subtree, subtree, then element.
  PlusOne  :: !Int
           -> !(BinomialTree ('Succ h) f x)
           -> !(BalancedTree h f y)
           -> BinomialTree h f (x <+> y)

  -- Contains size of the subtree, subtree, then element.
  PlusZero  :: !Int
            -> !(BinomialTree ('Succ h) f x)
            -> BinomialTree h f x

tsize :: BinomialTree h f a -> Int
tsize Empty = 0
tsize (PlusOne s _ _) = 2*s+1
tsize (PlusZero  s _) = 2*s

t_cnt_size :: BinomialTree h f a -> Int
t_cnt_size Empty = 0
t_cnt_size (PlusOne _ l r) = t_cnt_size l + bal_size r
t_cnt_size (PlusZero  _ l) = t_cnt_size l

-- | Concatenate a binomial tree and a balanced tree.
append :: BinomialTree h f x
       -> BalancedTree h f y
       -> BinomialTree h f (x <+> y)
append Empty y = PlusOne 0 Empty y
append (PlusOne _ t x) y =
  case assoc t x y of
    Refl ->
      let t' = append t (BalPair x y)
       in PlusZero (tsize t') t'
append (PlusZero s t) x = PlusOne s t x

instance TestEqualityFC (BinomialTree h) where
  testEqualityFC _ Empty Empty = return Refl
  testEqualityFC test (PlusZero _ x1) (PlusZero _ y1) = do
    Refl <- testEqualityFC test x1 y1
    return Refl
  testEqualityFC test (PlusOne _ x1 x2) (PlusOne _ y1 y2) = do
    Refl <- testEqualityFC test x1 y1
    Refl <- testEqualityFC test x2 y2
    return Refl
  testEqualityFC _ _ _ = Nothing

instance OrdFC (BinomialTree h) where
  compareFC _ Empty Empty = EQF
  compareFC _ Empty _ = LTF
  compareFC _ _ Empty = GTF

  compareFC test (PlusZero _ x1) (PlusZero _ y1) =
    joinOrderingF (compareFC test x1 y1) $ EQF
  compareFC _ PlusZero{} _ = LTF
  compareFC _ _ PlusZero{} = GTF

  compareFC test (PlusOne _ x1 x2) (PlusOne _ y1 y2) =
    joinOrderingF (compareFC test x1 y1) $
    joinOrderingF (compareFC test x2 y2) $
    EQF

instance HashableF f => HashableF (BinomialTree h f) where
  hashWithSaltF s t =
    case t of
      Empty -> s
      PlusZero _ x   -> s `hashWithSaltF` x
      PlusOne  _ x y -> s `hashWithSaltF` x `hashWithSaltF` y

-- | Map over a binary tree.
fmap_bin :: (forall tp . f tp -> g tp)
         -> BinomialTree h f c
         -> BinomialTree h g c
fmap_bin _ Empty = Empty
fmap_bin f (PlusOne s t x) = PlusOne s (fmap_bin f t) (fmap_bal f x)
fmap_bin f (PlusZero s t)  = PlusZero s (fmap_bin f t)
{-# INLINABLE fmap_bin #-}

traverse_bin :: Applicative m
             => (forall tp . f tp -> m (g tp))
             -> BinomialTree h f c
             -> m (BinomialTree h g c)
traverse_bin _ Empty = pure Empty
traverse_bin f (PlusOne s t x) = PlusOne s  <$> traverse_bin f t <*> traverse_bal f x
traverse_bin f (PlusZero s t)  = PlusZero s <$> traverse_bin f t
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
     in unsafeCoerce (PlusOne s t u)
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
        r = unsafeCoerce (PlusOne s) <$> t <*> u
     in r
  | otherwise =
    let s = sz `shiftR` 1
        t = unsafe_bin_generateM s (h+1) f
        r :: m (BinomialTree h f t)
        r = PlusZero s <$> t
     in r

------------------------------------------------------------------------
-- Dropping

data DropResult f (ctx :: Ctx k) where
  DropEmpty :: DropResult f EmptyCtx
  DropExt   :: BinomialTree 'Zero f x
            -> f y
            -> DropResult f (x ::> y)

-- | 'bal_drop x y' returns the tree formed 'append x (init y)'
bal_drop :: forall h f x y
          . BinomialTree h f x
            -- ^ Bina
         -> BalancedTree h f y
         -> DropResult f (x <+> y)
bal_drop t (BalLeaf e) = DropExt t e
bal_drop t (BalPair x y) =
  unsafeCoerce (bal_drop (PlusOne (tsize t) (unsafeCoerce t) x) y)

bin_drop :: forall h f ctx
          . BinomialTree h f ctx
         -> DropResult f ctx
bin_drop Empty = DropEmpty
bin_drop (PlusZero _ u) = bin_drop u
bin_drop (PlusOne s t u) =
  let m = case t of
            Empty -> Empty
            _ -> PlusZero s t
   in bal_drop m u

------------------------------------------------------------------------
-- Indexing

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
unsafe_bin_adjust :: forall m h f x y a b
                   . Functor m
                  => (f x -> m (f y))
                  -> BinomialTree h f a -- ^ Tree to lookup in.
                  -> Int
                  -> Int -- ^ Size of tree
                  -> m (BinomialTree h f b)
unsafe_bin_adjust _ Empty _ _ = error "unsafe_bin_adjust reached end of list"
unsafe_bin_adjust f (PlusOne sz t u) j i
  | sz == j `shiftR` (1+i) =
    unsafeCoerce . PlusOne sz t        <$> (unsafe_bal_adjust f u j i)
  | otherwise =
    unsafeCoerce . flip (PlusOne sz) u <$> (unsafe_bin_adjust f t j (i+1))
unsafe_bin_adjust f (PlusZero sz t) j i
  | sz == j `shiftR` (1+i) = error "unsafe_bin_adjust stopped at PlusZero"
  | otherwise = PlusZero sz <$> (unsafe_bin_adjust f t j (i+1))


{-# SPECIALIZE unsafe_bin_adjust
     :: (f x -> Identity (f y))
     -> BinomialTree h f a
     -> Int
     -> Int
     -> Identity (BinomialTree h f b)
  #-}

tree_zipWithM :: Applicative m
             => (forall x . f x -> g x -> m (h x))
             -> BinomialTree u f a
             -> BinomialTree u g a
             -> m (BinomialTree u h a)
tree_zipWithM _ Empty Empty = pure Empty
tree_zipWithM f (PlusOne s x1 x2) (PlusOne _ y1 y2) =
  PlusOne s <$> tree_zipWithM f x1 (unsafeCoerce y1)
            <*> bal_zipWithM  f x2 (unsafeCoerce y2)
tree_zipWithM f (PlusZero s x1) (PlusZero _ y1) =
  PlusZero s <$> tree_zipWithM f x1 y1
tree_zipWithM _ _ _ = error "ilegal args to tree_zipWithM"
{-# INLINABLE tree_zipWithM #-}

------------------------------------------------------------------------
-- Assignment

-- | An assignment is a sequence that maps each index with type 'tp' to
-- a value of type 'f tp'.
--
-- This assignment implementation uses a binomial tree implementation
-- that offers lookups and updates in time and space logarithmic with
-- respect to the number of elements in the context.
newtype Assignment (f :: k -> *) (ctx :: Ctx k)
      = Assignment (BinomialTree 'Zero f ctx)

type role Assignment nominal nominal

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

extend :: Assignment f ctx -> f x -> Assignment f (ctx ::> x)
extend (Assignment x) y = Assignment $ append x (BalLeaf y)

-- | Unexported index that returns an arbitrary type of expression.
unsafeIndex :: proxy u -> Int -> Assignment f ctx -> f u
unsafeIndex _ idx (Assignment t) = seq t $ unsafe_bin_index t idx 0

-- | Return value of assignment.
(!) :: Assignment f ctx -> Index ctx tp -> f tp
a ! Index i = assert (0 <= i && i < sizeInt (size a)) $
              unsafeIndex Proxy i a

-- | Return value of assignment, where the index is into an
--   initial sequence of the assignment.
(!^) :: KnownDiff l r => Assignment f r -> Index l tp -> f tp
a !^ i = a ! extendIndex i

instance TestEqualityFC Assignment where
   testEqualityFC test (Assignment x) (Assignment y) = do
     Refl <- testEqualityFC test x y
     return Refl

instance TestEquality f => TestEquality (Assignment f) where
  testEquality = testEqualityFC testEquality

instance TestEquality f => Eq (Assignment f ctx) where
  x == y = isJust (testEquality x y)

instance OrdFC Assignment where
  compareFC test (Assignment x) (Assignment y) =
     joinOrderingF (compareFC test x y) $ EQF

instance OrdF f => OrdF (Assignment f) where
  compareF = compareFC compareF

instance OrdF f => Ord (Assignment f ctx) where
  compare x y = toOrdering (compareF x y)

instance HashableF (Index ctx) where
  hashWithSaltF s i = hashWithSalt s (indexVal i)

instance Hashable (Index ctx tp) where
  hashWithSalt = hashWithSaltF

instance HashableF f => Hashable (Assignment f ctx) where
  hashWithSalt s (Assignment a) = hashWithSaltF s a

instance HashableF f => HashableF (Assignment f) where
  hashWithSaltF = hashWithSalt

instance ShowF f => Show (Assignment f ctx) where
  show a = "[" Prelude.++ intercalate ", " (toListFC showF a) Prelude.++ "]"

instance ShowF f => ShowF (Assignment f)

-- | Modify the value of an assignment at a particular index.
adjustM :: Functor m => (f tp -> m (f tp)) -> Index ctx tp -> Assignment f ctx -> m (Assignment f ctx)
adjustM f (Index i) (Assignment a) = Assignment <$> (unsafe_bin_adjust f a i 0)
{-# SPECIALIZE adjustM :: (f tp -> Identity (f tp)) -> Index ctx tp -> Assignment f ctx -> Identity (Assignment f ctx) #-}

type instance IndexF       (Assignment f ctx) = Index ctx
type instance IxValueF     (Assignment f ctx) = f

instance forall (f :: k -> *) ctx. IxedF' k (Assignment f ctx) where
  ixF' :: Index ctx x -> Lens.Lens' (Assignment f ctx) (f x)
  ixF' idx f = adjustM f idx

instance forall (f :: k -> *) ctx. IxedF k (Assignment f ctx) where
  ixF = ixF'

-- This is an unsafe version of update that changes the type of the expression.
unsafeUpdate :: Int -> Assignment f ctx -> f u -> Assignment f ctx'
unsafeUpdate i (Assignment a) e = Assignment (runIdentity (unsafe_bin_adjust (\_ -> Identity e) a i 0))

-- | View an assignment as either empty or an assignment with one appended.
data AssignView f ctx where
  AssignEmpty :: AssignView f EmptyCtx
  AssignExtend :: Assignment f ctx
               -> f tp
               -> AssignView f (ctx::>tp)

-- | View an assignment as either empty or an assignment with one appended.
viewAssign :: forall f ctx . Assignment f ctx -> AssignView f ctx
viewAssign (Assignment x) =
  case bin_drop x of
    DropEmpty -> AssignEmpty
    DropExt t v -> AssignExtend (Assignment t) v

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
-- Appending

appendBal :: Assignment f x -> BalancedTree h f y -> Assignment f (x <+> y)
appendBal x (BalLeaf a) = x `extend` a
appendBal x (BalPair y z) =
  case assoc x y z of
    Refl -> x `appendBal` y `appendBal` z

appendBin :: Assignment f x -> BinomialTree h f y -> Assignment f (x <+> y)
appendBin x Empty = x
appendBin x (PlusOne _ y z) =
  case assoc x y z of
    Refl -> x `appendBin` y `appendBal` z
appendBin x (PlusZero _ y) = x `appendBin` y

(<++>) :: Assignment f x -> Assignment f y -> Assignment f (x <+> y)
x <++> Assignment y = x `appendBin` y

------------------------------------------------------------------------
-- KnownRepr instances

instance (KnownRepr (Assignment f) ctx, KnownRepr f bt)
      => KnownRepr (Assignment f) (ctx ::> bt) where
  knownRepr = knownRepr `extend` knownRepr

instance KnownRepr (Assignment f) EmptyCtx where
  knownRepr = empty

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
