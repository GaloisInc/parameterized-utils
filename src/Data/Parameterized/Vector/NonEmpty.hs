{-# Language GADTs, DataKinds, TypeOperators, BangPatterns #-}
{-# Language PatternGuards #-}
{-# Language PolyKinds #-}
{-# Language TypeApplications, ScopedTypeVariables #-}
{-# Language TupleSections #-}
{-# Language Rank2Types, RoleAnnotations #-}
{-# Language CPP #-}
#if __GLASGOW_HASKELL__ >= 805
{-# Language NoStarIsType #-}
#endif
{-|
Copyright        : (c) Galois, Inc 2014-2019

A fixed-size vector of typed elements.

NB: This module contains an orphan instance. It will be included in GHC 8.10,
see https://gitlab.haskell.org/ghc/ghc/merge_requests/273.
-}
module Data.Parameterized.Vector.NonEmpty
  ( Vector
    -- * Lists
  , fromList
  , toList

    -- * Assignments
  , fromAssignment
  , toAssignment

    -- * Length
  , length
  , nonEmpty
  , lengthInt

    -- * Indexing
  , elemAt
  , elemAtMaybe
  , elemAtUnsafe

    -- * Update
  , insertAt
  , insertAtMaybe

    -- * Sub sequences
  , uncons
  , unsnoc
  , slice
  , Data.Parameterized.Vector.NonEmpty.take
  , replace
  , mapAt
  , mapAtM

    -- * Zipping
  , zipWith
  , zipWithM
  , zipWithM_
  , interleave

    -- * Reorder
  , shuffle
  , reverse
  , rotateL
  , rotateR
  , shiftL
  , shiftR

    -- * Construction
  , singleton
  , cons
  , snoc
  , generate
  , generateM
  -- ** Unfolding
  , unfoldr
  , unfoldrM
  , unfoldrWithIndex
  , unfoldrWithIndexM

    -- * Splitting and joining
    -- ** General
  , joinWithM
  , joinWith
  , splitWith
  , splitWithA

    -- ** Vectors
  , split
  , join
  , append

  ) where

import qualified Data.Vector as Vector
import Data.Functor.Compose
import Data.Coerce
import Data.Vector.Mutable (MVector)
import qualified Data.Vector.Mutable as MVector
import Control.Monad.ST
import Data.Functor.Identity
import Data.Parameterized.NatRepr
import Data.Parameterized.NatRepr.Internal
import Data.Proxy
import Prelude hiding (length,reverse,zipWith)
import Numeric.Natural

import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Utils.Endian

-- | Fixed-size non-empty vectors.
data Vector n a where
  Vector :: (1 <= n) => !(Vector.Vector a) -> Vector n a

type role Vector nominal representational

instance Eq a => Eq (Vector n a) where
  (Vector x) == (Vector y) = x == y

instance Show a => Show (Vector n a) where
  show (Vector x) = show x

-- | Get the elements of the vector as a list, lowest index first.
toList :: Vector n a -> [a]
toList (Vector v) = Vector.toList v
{-# Inline toList #-}

-- NOTE: We are using the raw 'NatRepr' constructor here, which is unsafe.
-- | Length of the vector.
-- @O(1)@
length :: Vector n a -> NatRepr n
length (Vector xs) = NatRepr (fromIntegral (Vector.length xs) :: Natural)
{-# INLINE length #-}

-- | The length of the vector as an "Int".
lengthInt :: Vector n a -> Int
lengthInt (Vector xs) = Vector.length xs
{-# Inline lengthInt #-}

elemAt :: ((i+1) <= n) => NatRepr i -> Vector n a -> a
elemAt n (Vector xs) = xs Vector.! widthVal n

-- | Get the element at the given index.
-- @O(1)@
elemAtMaybe :: Int -> Vector n a -> Maybe a
elemAtMaybe n (Vector xs) = xs Vector.!? n
{-# INLINE elemAt #-}

-- | Get the element at the given index.
-- Raises an exception if the element is not in the vector's domain.
-- @O(1)@
elemAtUnsafe :: Int -> Vector n a -> a
elemAtUnsafe n (Vector xs) = xs Vector.! n
{-# INLINE elemAtUnsafe #-}


-- | Insert an element at the given index.
-- @O(n)@.
insertAt :: ((i + 1) <= n) => NatRepr i -> a -> Vector n a -> Vector n a
insertAt n a (Vector xs) = Vector (Vector.unsafeUpd xs [(widthVal n,a)])

-- | Insert an element at the given index.
-- Return 'Nothing' if the element is outside the vector bounds.
-- @O(n)@.
insertAtMaybe :: Int -> a -> Vector n a -> Maybe (Vector n a)
insertAtMaybe n a (Vector xs)
  | 0 <= n && n < Vector.length xs = Just (Vector (Vector.unsafeUpd xs [(n,a)]))
  | otherwise = Nothing


-- | Proof that the length of this vector is not 0.
nonEmpty :: Vector n a -> LeqProof 1 n
nonEmpty (Vector _) = LeqProof
{-# Inline nonEmpty #-}


-- | Remove the first element of the vector, and return the rest, if any.
uncons :: forall n a.  Vector n a -> (a, Either (n :~: 1) (Vector (n-1) a))
uncons v@(Vector xs) = (Vector.head xs, mbTail)
  where
  mbTail :: Either (n :~: 1) (Vector (n - 1) a)
  mbTail = case testStrictLeq (knownNat @1) (length v) of
             Left n2_leq_n ->
               do LeqProof <- return (leqSub2 n2_leq_n (leqRefl (knownNat @1)))
                  return (Vector (Vector.tail xs))
             Right Refl    -> Left Refl
{-# Inline uncons #-}

-- | Remove the last element of the vector, and return the rest, if any.
unsnoc :: forall n a.  Vector n a -> (a, Either (n :~: 1) (Vector (n-1) a))
unsnoc v@(Vector xs) = (Vector.last xs, mbTail)
  where
  mbTail :: Either (n :~: 1) (Vector (n - 1) a)
  mbTail = case testStrictLeq (knownNat @1) (length v) of
             Left n2_leq_n ->
               do LeqProof <- return (leqSub2 n2_leq_n (leqRefl (knownNat @1)))
                  return (Vector (Vector.slice 0 (Vector.length xs - 1) xs))
             Right Refl    -> Left Refl
{-# Inline unsnoc #-}


--------------------------------------------------------------------------------

-- | Make a vector of the given length and element type.
-- Returns "Nothing" if the input list does not have the right number of
-- elements.
-- @O(n)@.
fromList :: (1 <= n) => NatRepr n -> [a] -> Maybe (Vector n a)
fromList n xs
  | widthVal n == Vector.length v = Just (Vector v)
  | otherwise                     = Nothing
  where
  v = Vector.fromList xs
{-# INLINE fromList #-}

-- | Convert a non-empty 'Ctx.Assignment' to a fixed-size 'Vector'.
--
-- This function uses the same ordering convention as 'Ctx.toVector'.
fromAssignment ::
  forall f ctx tp e.
  (forall tp'. f tp' -> e) ->
  Ctx.Assignment f (ctx Ctx.::> tp) ->
  Vector (Ctx.CtxSize (ctx Ctx.::> tp)) e
fromAssignment f assign =
  case Ctx.viewAssign assign of
    Ctx.AssignExtend assign' _ ->
      case leqAdd (leqRefl (knownNat @1)) (Ctx.sizeToNatRepr (Ctx.size assign')) of
        LeqProof -> Vector (Ctx.toVector assign f)

-- | Convert a 'Vector' into a 'Ctx.Assignment'.
--
-- This function uses the same ordering convention as 'Ctx.toVector'.
toAssignment ::
  Ctx.Size ctx ->
  (forall tp. Ctx.Index ctx tp -> e -> f tp) ->
  Vector (Ctx.CtxSize ctx) e ->
  Ctx.Assignment f ctx
toAssignment sz g vec =
  -- The unsafe indexing here relies on the safety of the rest of the Vector
  -- API, specifically the inability to construct vectors that have an
  -- underlying size that differs from the size in their type.
  Ctx.generate sz (\idx -> g idx (elemAtUnsafe (Ctx.indexVal idx) vec))

-- | Extract a subvector of the given vector.
slice :: (i + w <= n, 1 <= w) =>
            NatRepr i {- ^ Start index -} ->
            NatRepr w {- ^ Width of sub-vector -} ->
            Vector n a -> Vector w a
slice i w (Vector xs) = Vector (Vector.slice (widthVal i) (widthVal w) xs)
{-# INLINE slice #-}

-- | Take the front (lower-indexes) part of the vector.
take :: forall n x a. (1 <= n) => NatRepr n -> Vector (n + x) a -> Vector n a
take | LeqProof <- prf = slice (knownNat @0)
  where
  prf = leqAdd (leqRefl (Proxy @n)) (Proxy @x)

-- | Scope a monadic function to a sub-section of the given vector.
mapAtM :: Monad m => (i + w <= n, 1 <= w) =>
            NatRepr i {- ^ Start index -} ->
            NatRepr w {- ^ Section width -} ->
            (Vector w a -> m (Vector w a)) {-^ map for the sub-vector -} ->
            Vector n a -> m (Vector n a)
mapAtM i w f (Vector vn) =
  let
    (vhead, vtail) = Vector.splitAt (widthVal i) vn
    (vsect, vend) = Vector.splitAt (widthVal w) vtail
  in do
    Vector vsect' <- f (Vector vsect)
    return $ Vector $ vhead Vector.++ vsect' Vector.++ vend

-- | Scope a function to a sub-section of the given vector.
mapAt :: (i + w <= n, 1 <= w) =>
            NatRepr i {- ^ Start index -} ->
            NatRepr w {- ^ Section width -} ->
            (Vector w a -> Vector w a) {-^ map for the sub-vector -} ->
            Vector n a -> Vector n a
mapAt i w f vn = runIdentity $ mapAtM i w (pure . f) vn

-- | Replace a sub-section of a vector with the given sub-vector.
replace :: (i + w <= n, 1 <= w) =>
              NatRepr i {- ^ Start index -} ->
              Vector w a {- ^ sub-vector -} ->
              Vector n a -> Vector n a
replace i vw vn = mapAt i (length vw) (const vw) vn

--------------------------------------------------------------------------------

instance Functor (Vector n) where
  fmap f (Vector xs) = Vector (Vector.map f xs)
  {-# Inline fmap #-}

instance Foldable (Vector n) where
  foldMap f (Vector xs) = foldMap f xs

instance Traversable (Vector n) where
  traverse f (Vector xs) = Vector <$> traverse f xs
  {-# Inline traverse #-}

-- | Zip two vectors, potentially changing types.
-- @O(n)@
zipWith :: (a -> b -> c) -> Vector n a -> Vector n b -> Vector n c
zipWith f (Vector xs) (Vector ys) = Vector (Vector.zipWith f xs ys)
{-# Inline zipWith #-}

zipWithM :: Monad m => (a -> b -> m c) ->
                       Vector n a -> Vector n b -> m (Vector n c)
zipWithM f (Vector xs) (Vector ys) = Vector <$> Vector.zipWithM f xs ys
{-# Inline zipWithM #-}

zipWithM_ :: Monad m => (a -> b -> m ()) -> Vector n a -> Vector n b -> m ()
zipWithM_ f (Vector xs) (Vector ys) = Vector.zipWithM_ f xs ys
{-# Inline zipWithM_ #-}

{- | Interleave two vectors.  The elements of the first vector are
at even indexes in the result, the elements of the second are at odd indexes. -}
interleave ::
  forall n a. (1 <= n) => Vector n a -> Vector n a -> Vector (2 * n) a
interleave (Vector xs) (Vector ys)
  | LeqProof <- leqMulPos (Proxy @2) (Proxy @n) = Vector zs
  where
  len = Vector.length xs + Vector.length ys
  zs  = Vector.generate len (\i -> let v = if even i then xs else ys
                                   in v Vector.! (i `div` 2))


--------------------------------------------------------------------------------

{- | Move the elements around, as specified by the given function.
  * Note: the reindexing function says where each of the elements
          in the new vector come from.
  * Note: it is OK for the same input element to end up in mulitple places
          in the result.
@O(n)@
-}
shuffle :: (Int -> Int) -> Vector n a -> Vector n a
shuffle f (Vector xs) = Vector ys
  where
  ys = Vector.generate (Vector.length xs) (\i -> xs Vector.! f i)
{-# Inline shuffle #-}

-- | Reverse the vector.
reverse :: forall a n. (1 <= n) => Vector n a -> Vector n a
reverse x = shuffle (\i -> lengthInt x - i - 1) x

-- | Rotate "left".  The first element of the vector is on the "left", so
-- rotate left moves all elemnts toward the corresponding smaller index.
-- Elements that fall off the beginning end up at the end.
rotateL :: Int -> Vector n a -> Vector n a
rotateL !n xs = shuffle rotL xs
  where
  !len   = lengthInt xs
  rotL i = (i + n) `mod` len          -- `len` is known to be >= 1
{-# Inline rotateL #-}

-- | Rotate "right".  The first element of the vector is on the "left", so
-- rotate right moves all elemnts toward the corresponding larger index.
-- Elements that fall off the end, end up at the beginning.
rotateR :: Int -> Vector n a -> Vector n a
rotateR !n xs = shuffle rotR xs
  where
  !len   = lengthInt xs
  rotR i = (i - n) `mod` len        -- `len` is known to be >= 1
{-# Inline rotateR #-}

{- | Move all elements towards smaller indexes.
Elements that fall off the front are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
shiftL :: Int -> a -> Vector n a -> Vector n a
shiftL !x a (Vector xs) = Vector ys
  where
  !len = Vector.length xs
  ys   = Vector.generate len (\i -> let j = i + x
                                    in if j >= len then a else xs Vector.! j)
{-# Inline shiftL #-}

{- | Move all elements towards the larger indexes.
Elements that "fall" off the end are ignored.
Empty slots are filled in with the given element.
@O(n)@. -}
shiftR :: Int -> a -> Vector n a -> Vector n a
shiftR !x a (Vector xs) = Vector ys
  where
  !len = Vector.length xs
  ys   = Vector.generate len (\i -> let j = i - x
                                    in if j < 0 then a else xs Vector.! j)
{-# Inline shiftR #-}

-------------------------------------------------------------------------------i

-- | Append two vectors. The first one is at lower indexes in the result.
append :: Vector m a -> Vector n a -> Vector (m + n) a
append v1@(Vector xs) v2@(Vector ys) =
  case leqAddPos (length v1) (length v2) of { LeqProof ->
    Vector (xs Vector.++ ys)
  }
{-# Inline append #-}

--------------------------------------------------------------------------------
-- Constructing Vectors

-- | Vector with exactly one element
singleton :: forall a. a -> Vector 1 a
singleton a = Vector (Vector.singleton a)

leqLen :: forall n a. Vector n a -> LeqProof 1 (n + 1)
leqLen v =
  let leqSucc :: forall f z. f z -> LeqProof z (z + 1)
      leqSucc fz = leqAdd (leqRefl fz :: LeqProof z z) (knownNat @1)
  in leqTrans (nonEmpty v :: LeqProof 1 n) (leqSucc (length v))

-- | Add an element to the head of a vector
cons :: forall n a. a -> Vector n a -> Vector (n+1) a
cons a v@(Vector x) = case leqLen v of LeqProof -> (Vector (Vector.cons a x))

-- | Add an element to the tail of a vector
snoc :: forall n a. Vector n a -> a -> Vector (n+1) a
snoc v@(Vector x) a = case leqLen v of LeqProof -> (Vector (Vector.snoc x a))

-- | This newtype wraps Vector so that we can curry it in the call to
-- @natRecBounded@. It adds 1 to the length so that the base case is
-- a @Vector@ of non-zero length.
newtype Vector' a n = MkVector' (Vector (n+1) a)

unVector' :: Vector' a n -> Vector (n+1) a
unVector' (MkVector' v) = v

generate' :: forall h a
           . NatRepr h
          -> (forall n. (n <= h) => NatRepr n -> a)
          -> Vector' a h
generate' h gen =
  runIdentity $ unfoldrWithIndexM' h (\n _last -> Identity (gen n, ())) ()

-- | Apply a function to each element in a range starting at zero;
-- return the a vector of values obtained.
-- cf. both @natFromZero@ and @Data.Vector.generate@
generate :: forall h a
          . NatRepr h
         -> (forall n. (n <= h) => NatRepr n -> a)
         -> Vector (h + 1) a
generate h gen = unVector' (generate' h gen)

-- | Since @Vector@ is traversable, we can pretty trivially sequence
-- @natFromZeroVec@ inside a monad.
generateM :: forall m h a. (Monad m)
          => NatRepr h
          -> (forall n. (n <= h) => NatRepr n -> m a)
          -> m (Vector (h + 1) a)
generateM h gen = sequence $ generate h gen

newtype Compose3 m f g a = Compose3 { getCompose3 :: m (f (g a)) }

unfoldrWithIndexM' :: forall m h a b. (Monad m)
                  => NatRepr h
                  -> (forall n. (n <= h) => NatRepr n -> b -> m (a, b))
                  -> b
                  -> m (Vector' a h)
unfoldrWithIndexM' h gen start =
  case isZeroOrGT1 h of
    Left Refl -> snd <$> getCompose3 base
    Right LeqProof ->
      case (minusPlusCancel h (knownNat @1) :: h - 1 + 1 :~: h) of { Refl ->
        snd <$> getCompose3 (natRecBounded (decNat h) (decNat h) base step)
      }
  where base :: Compose3 m ((,) b) (Vector' a) 0
        base = Compose3 $ (\(hd, b) -> (b, MkVector' (singleton hd))) <$> gen (knownNat @0) start
        step :: forall p. (1 <= h, p <= h - 1)
             => NatRepr p
             -> Compose3 m ((,) b) (Vector' a) p
             -> Compose3 m ((,) b) (Vector' a) (p + 1)
        step p (Compose3 mv) =
          case minusPlusCancel h (knownNat @1) :: h - 1 + 1 :~: h of { Refl ->
          case (leqAdd2 (LeqProof :: LeqProof p (h-1))
                        (LeqProof :: LeqProof 1 1) :: LeqProof (p+1) h) of { LeqProof ->
            Compose3 $
              do (seed, MkVector' v) <- mv
                 (next, nextSeed) <- gen (incNat p) seed
                 pure $ (nextSeed, MkVector' $ snoc v next)
          }}

-- | Monadically unfold a vector, with access to the current index.
--
-- c.f. @Data.Vector.unfoldrExactNM@
unfoldrWithIndexM :: forall m h a b. (Monad m)
                 => NatRepr h
                 -> (forall n. (n <= h) => NatRepr n -> b -> m (a, b))
                 -> b
                 -> m (Vector (h + 1) a)
unfoldrWithIndexM h gen start = unVector' <$> unfoldrWithIndexM' h gen start

-- | Unfold a vector, with access to the current index.
--
-- c.f. @Data.Vector.unfoldrExactN@
unfoldrWithIndex :: forall h a b
                . NatRepr h
                -> (forall n. (n <= h) => NatRepr n -> b -> (a, b))
                -> b
                -> Vector (h + 1) a
unfoldrWithIndex h gen start =
  unVector' $ runIdentity $ unfoldrWithIndexM' h (\n v -> Identity (gen n v)) start

-- | Monadically construct a vector with exactly @h + 1@ elements by repeatedly
-- applying a generator function to a seed value.
--
-- c.f. @Data.Vector.unfoldrExactNM@
unfoldrM :: forall m h a b. (Monad m)
        => NatRepr h
        -> (b -> m (a, b))
        -> b
        -> m (Vector (h + 1) a)
unfoldrM h gen start = unfoldrWithIndexM h (\_ v -> gen v) start

-- | Construct a vector with exactly @h + 1@ elements by repeatedly applying a
-- generator function to a seed value.
--
-- c.f. @Data.Vector.unfoldrExactN@
unfoldr :: forall h a b
        . NatRepr h
       -> (b -> (a, b))
       -> b
       -> Vector (h + 1) a
unfoldr h gen start = unfoldrWithIndex h (\_ v -> gen v) start

--------------------------------------------------------------------------------

coerceVec :: Coercible a b => Vector n a -> Vector n b
coerceVec = coerce

-- | Monadically join a vector of values, using the given function.
-- This functionality can sometimes be reproduced by creating a newtype
-- wrapper and using @joinWith@, this implementation is provided for
-- convenience.
joinWithM ::
  forall m f n w.
  (1 <= w, Monad m) =>
  (forall l. (1 <= l) => NatRepr l -> f w -> f l -> m (f (w + l)))
  {- ^ A function for joining contained elements.  The first argument is
       the size of the accumulated third term, and the second argument
       is the element to join to the accumulated term.  The function
       can use any join strategy desired (prepending/"BigEndian",
       appending/"LittleEndian", etc.). -}
  -> NatRepr w
  -> Vector n (f w)
  -> m (f (n * w))

joinWithM jn w = fmap fst . go
  where
  go :: forall l. Vector l (f w) -> m (f (l * w), NatRepr (l * w))
  go exprs =
    case uncons exprs of
      (a, Left Refl) -> return (a, w)
      (a, Right rest) ->
        case nonEmpty rest                of { LeqProof ->
        case leqMulPos (length rest) w    of { LeqProof ->
        case nonEmpty exprs               of { LeqProof ->
        case lemmaMul w (length exprs)    of { Refl -> do
          -- @siddharthist: This could probably be written applicatively?
          (res, sz) <- go rest
          joined <- jn sz a res
          return (joined, addNat w sz)
        }}}}

-- | Join a vector of vectors, using the given function to combine the
-- sub-vectors.
joinWith ::
  forall f n w.
  (1 <= w) =>
  (forall l. (1 <= l) => NatRepr l -> f w -> f l -> f (w + l))
  {- ^ A function for joining contained elements.  The first argument is
       the size of the accumulated third term, and the second argument
       is the element to join to the accumulated term.  The function
       can use any join strategy desired (prepending/"BigEndian",
       appending/"LittleEndian", etc.). -}
  -> NatRepr w
  -> Vector n (f w)
  -> f (n * w)
joinWith jn w v = runIdentity $ joinWithM (\n x -> pure . (jn n x)) w v
{-# Inline joinWith #-}

-- | Split a vector into a vector of vectors.
--
-- The "Endian" parameter determines the ordering of the inner
-- vectors.  If "LittleEndian", then less significant bits go into
-- smaller indexes.  If "BigEndian", then less significant bits go
-- into larger indexes.  See the documentation for 'split' for more
-- details.
splitWith :: forall f w n.
  (1 <= w, 1 <= n) =>
  Endian ->
  (forall i. (i + w <= n * w) =>
             NatRepr (n * w) -> NatRepr i -> f (n * w) -> f w)
  {- ^ A function for slicing out a chunk of length @w@, starting at @i@ -} ->
  NatRepr n -> NatRepr w -> f (n * w) -> Vector n (f w)
splitWith endian select n w val = Vector (Vector.create initializer)
  where
  len          = widthVal n
  start :: Int
  next :: Int -> Int
  (start,next) = case endian of
                   LittleEndian -> (0, succ)
                   BigEndian    -> (len - 1, pred)

  initializer :: forall s. ST s (MVector s (f w))
  initializer =
    do LeqProof <- return (leqMulPos n w)
       LeqProof <- return (leqMulMono n w)

       v <- MVector.new len
       let fill :: Int -> NatRepr i -> ST s ()
           fill loc i =
             let end = addNat i w in
             case testLeq end inLen of
               Just LeqProof ->
                 do MVector.write v loc (select inLen i val)
                    fill (next loc) end
               Nothing -> return ()


       fill start (knownNat @0)
       return v

  inLen :: NatRepr (n * w)
  inLen = natMultiply n w
{-# Inline splitWith #-}

-- We can sneakily put our functor in the parameter "f" of @splitWith@ using the
-- @Compose@ newtype.
-- | An applicative version of @splitWith@.
splitWithA :: forall f g w n. (Applicative f, 1 <= w, 1 <= n) =>
  Endian ->
  (forall i. (i + w <= n * w) =>
             NatRepr (n * w) -> NatRepr i -> g (n * w) -> f (g w))
  {- ^ f function for slicing out f chunk of length @w@, starting at @i@ -} ->
  NatRepr n -> NatRepr w -> g (n * w) -> f (Vector n (g w))
splitWithA e select n w val = traverse getCompose $
  splitWith @(Compose f g) e select' n w $ Compose (pure val)
  where -- Wrap everything in Compose
        select' :: (forall i. (i + w <= n * w)
                => NatRepr (n * w) -> NatRepr i -> Compose f g (n * w) -> Compose f g w)
        -- Whatever we pass in as "val" is what's passed to select anyway,
        -- so there's no need to examine the argument. Just use "val" directly here.
        select' nw i _ = Compose $ select nw i val

newtype Vec a n = Vec (Vector n a)

vSlice :: (i + w <= l, 1 <= w) =>
  NatRepr w -> NatRepr l -> NatRepr i -> Vec a l -> Vec a w
vSlice w _ i (Vec xs) = Vec (slice i w xs)
{-# Inline vSlice #-}

-- | Append the two bit vectors.  The first argument is
-- at the lower indexes of the resulting vector.
vAppend :: NatRepr n -> Vec a m -> Vec a n -> Vec a (m + n)
vAppend _ (Vec xs) (Vec ys) = Vec (append xs ys)
{-# Inline vAppend #-}

-- | Split a vector into a vector of vectors.  The default ordering of
-- the outer result vector is "LittleEndian".
--
-- For example:
-- @
--   let wordsize = knownNat :: NatRepr 3
--       vecsize = knownNat :: NatRepr 12
--       numwords = knownNat :: NatRepr 4  (12 / 3)
--       Just inpvec = fromList vecsize [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ]
--   in show (split numwords wordsize inpvec) == "[ [1,2,3], [4,5,6], [7,8,9], [10,11,12] ]"
-- @
-- whereas a BigEndian result would have been
-- @
--      [ [10,11,12], [7,8,9], [4,5,6], [1,2,3] ]
-- @
split :: (1 <= w, 1 <= n) =>
         NatRepr n -- ^ Inner vector size
      -> NatRepr w -- ^ Outer vector size
      -> Vector (n * w) a -- ^ Input vector
      -> Vector n (Vector w a)
split n w xs = coerceVec (splitWith LittleEndian (vSlice w) n w (Vec xs))
{-# Inline split #-}

-- | Join a vector of vectors into a single vector.  Assumes an
-- append/"LittleEndian" join strategy: the order of the inner vectors
-- is preserved in the result vector.
--
-- @
--   let innersize = knownNat :: NatRepr 4
--       Just inner1 = fromList innersize [ 1, 2, 3, 4 ]
--       Just inner2 = fromList innersize [ 5, 6, 7, 8 ]
--       Just inner3 = fromList innersize [ 9, 10, 11, 12 ]
--       outersize = knownNat :: NatRepr 3
--       Just outer = fromList outersize [ inner1, inner2, inner3 ]
--   in show (join innersize outer) = [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ]
-- @
-- a prepend/"BigEndian" join strategy would have the result:
-- @
--   [ 9, 10, 11, 12, 5, 6, 7, 8, 1, 2, 3, 4 ]
-- @
join :: (1 <= w) => NatRepr w -> Vector n (Vector w a) -> Vector (n * w) a
join w xs = ys
  where Vec ys = joinWith vAppend w (coerceVec xs)
{-# Inline join #-}
