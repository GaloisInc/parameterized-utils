{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# Language CPP #-}
{-# Language DataKinds #-}
{-# Language ExplicitForAll #-}
{-# Language FlexibleInstances #-}
{-# Language LambdaCase #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
#if __GLASGOW_HASKELL__ >= 805
{-# Language NoStarIsType #-}
#endif
module Test.Vector
  ( vecTests
  )
where

import           Data.Functor.Const (Const(..))
import           Data.Functor.WithIndex (imap)
import           Data.Foldable.WithIndex (ifoldMap)
import           Data.Maybe (isJust)
import qualified Data.List as List
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.Vector
import           Data.Semigroup
import           GHC.TypeLits
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range
import           Numeric.Natural (Natural)
import           Prelude hiding (take, reverse, length)
import qualified Prelude as P
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Context (genSomePayloadList, mkUAsgn)


data SomeVector a = forall n. SomeVector (Vector n a)

instance Show a => Show (SomeVector a) where
  show (SomeVector v) = show v

genVectorOfLength :: (Monad m) => NatRepr n -> GenT m a -> GenT m (Vector (n + 1) a)
genVectorOfLength n genElem =
  do let w = widthVal n
     l <- HG.list (linear (w + 1) (w + 1)) genElem
     case testLeq (knownNat @1) (incNat n) of
       Nothing -> error "testLeq in genSomeVector"
       Just LeqProof ->
         case fromList (incNat n) l of
           Just v -> return v
           Nothing -> error ("fromList failure for size " <> show w)

genSomeVector :: (Monad m) => GenT m a -> GenT m (SomeVector a)
genSomeVector genElem =
  do Some len <- mkNatRepr <$> HG.integral (linear 0 (99 :: Natural))
     SomeVector <$> genVectorOfLength len genElem


genVectorKnownLength :: (1 <= n, KnownNat n, Monad m) => GenT m a -> GenT m (Vector n a)
genVectorKnownLength genElem =
  do let n = knownNat
         w = widthVal n
     l <- HG.list (constant w w) genElem
     case fromList n l of
       Just v -> return v
       Nothing -> error ("fromList failure for size " <> show w)

genOrdering :: Monad m => GenT m Ordering
genOrdering = HG.element [ LT, EQ, GT ]

genVectorIndex :: Monad m => NatRepr n -> GenT m (VectorIndex (n + 1))
genVectorIndex n =
  do i <- HG.int (linear 0 (fromIntegral (intValue n - 1)))
     pure $ elemAtUnsafe i (indicesUpTo n)

instance Show (a -> b) where
  show _ = "unshowable"

orderToOrder :: [Ordering -> Ordering]
orderToOrder =
  [ const EQ
  , id
  , \case
      EQ -> EQ
      LT -> GT
      GT -> LT
  , \case
      LT -> EQ
      EQ -> GT
      GT -> LT
  ]

-- We use @Ordering@ just because it's simple
vecTests :: IO TestTree
vecTests = testGroup "Vector" <$> return
  [ testProperty "reverse100" $ property $
    do SomeVector v <- forAll $ genSomeVector genOrdering
       case testLeq (knownNat @1) (length v) of
         Nothing -> pure ()
         Just LeqProof -> v === (reverse $ reverse v)
  , testProperty "reverseSingleton" $ property $
    do l <- (:[]) <$> forAll genOrdering
       Just v <- return $ fromList (knownNat @1) l
       v === reverse v

  , testProperty "split-join" $ property $
    do let n = knownNat @5
       v <- forAll $ genVectorKnownLength @(5 * 5) genOrdering
       v === (join n $ split n (knownNat @5) v)

  -- @cons@ is the same for vectors or lists
  , testProperty "cons" $ property $
    do let n = knownNat @20
           w = widthVal n
       l <- forAll $ HG.list (constant w w) genOrdering
       x <- forAll genOrdering
       (cons x <$> fromList n l) === fromList (incNat n) (x:l)

  -- @snoc@ is like appending to a list
  , testProperty "snoc" $ property $
    do let n = knownNat @20
           w = widthVal n
       l <- forAll $ HG.list (constant w w) genOrdering
       x <- forAll genOrdering
       (flip snoc x <$> fromList n l) === fromList (incNat n) (l ++ [x])

  -- @snoc@ and @unsnoc@ are inverses
  , testProperty "snoc/unsnoc" $ property $
    do let n = knownNat @20
           w = widthVal n
       l <- forAll $ HG.list (constant w w) genOrdering
       x <- forAll genOrdering
       (fst  . unsnoc . flip snoc x <$> fromList n l) === Just x

  -- @generate@ is like mapping a function over indices
  , testProperty "generate" $ property $
    do let n = knownNat @55
           w = widthVal n
           funs :: [ Int -> Ordering ]  -- some miscellaneous functions to generate Vector values
           funs =  [ const EQ
                   , \i -> if i < 10 then LT else if i > 15 then GT else EQ
                   , \i -> if i == 0 then EQ else GT
                   ]
       f <- forAll $ HG.element funs
       Just (generate n (f . widthVal)) === fromList (incNat n) (map f [0..w])

  -- @unfold@ works like @unfold@ on lists
  , testProperty "unfold" $ property $
    do let n = knownNat @55
           w = widthVal n
           funs :: [ Ordering -> (Ordering, Ordering) ]  -- some miscellaneous functions to generate Vector values
           funs =  [ const (EQ, EQ)
                   , \case
                       LT -> (LT, GT)
                       GT -> (GT, LT)
                       EQ -> (EQ, EQ)
                   ]
       f <- forAll $ HG.element funs
       o <- forAll $ HG.element [EQ, LT, GT]
       Just (unfoldr n f o) === fromList (incNat n) (P.take (w + 1) (List.unfoldr (Just . f) o))

  -- Converting to and from assignments preserves size and last element
  , testProperty "to-from-assignment" $ property $
    do vals <- forAll genSomePayloadList
       Some a <- return $ mkUAsgn vals
       let sz = Ctx.size a
       case Ctx.viewSize sz of
         Ctx.ZeroSize -> pure ()
         Ctx.IncSize _ ->
           let a' =
                 toAssignment
                   sz
                   (\_idx val -> Const val)
                   (fromAssignment Some a)
           in do assert $
                   isJust $
                     testEquality
                       (Ctx.sizeToNatRepr sz)
                       (Ctx.sizeToNatRepr (Ctx.size a'))
                 viewSome
                   (\lastElem ->
                      assert $
                        isJust $
                          testEquality
                            (a Ctx.! Ctx.lastIndex sz) lastElem)
                   (getConst (a' Ctx.! Ctx.lastIndex sz))

  , testProperty "fmap-id" $ property $
    do SomeVector v <- forAll $ genSomeVector genOrdering
       fmap id v === v

  , testProperty "fmap-compose" $ property $
    do SomeVector v <- forAll $ genSomeVector genOrdering
       f <- forAll $ HG.element orderToOrder
       g <- forAll $ HG.element orderToOrder
       fmap (g . f) v === fmap g (fmap f v)

  , testProperty "iterateN-range" $ property $
    do Some len <- mkNatRepr <$> forAll (HG.integral (linear 0 (99 :: Natural)))
       toList (iterateN len (+1) 0) === [0..(natValue len)]

  , testProperty "indicesOf-range" $ property $
    do SomeVector v <- forAll $ genSomeVector genOrdering
       toList (fmap indexValue (indicesOf v)) === [0..(natValue (length v) - 1)]

  , testProperty "imap-const" $ property $
    do f <- forAll $ HG.element orderToOrder
       SomeVector v <- forAll $ genSomeVector genOrdering
       imap (const f) v === fmap f v

  , testProperty "ifoldMap-const" $ property $
    do let funs :: [ Ordering -> String ]
           funs = [const "s", show]
       f <- forAll $ HG.element funs
       SomeVector v <- forAll $ genSomeVector genOrdering
       ifoldMap (const f) v === foldMap f v

  , testProperty "imap-const-indicesOf" $ property $
    do SomeVector v <- forAll $ genSomeVector genOrdering
       imap const v === indicesOf v

  , testProperty "imap-elemAt" $ property $
    do SomeVector v <- forAll $ genSomeVector genOrdering
       imap (\(VectorIndex i) _ -> elemAt i v) v === v

  , testProperty "Eq-VectorIndex-reflexive" $ property $
    do i <- forAll $ genVectorIndex (knownNat @10)
       i === i

  , testProperty "Eq-VectorIndex-symmetric" $ property $
    do i <- forAll $ genVectorIndex (knownNat @10)
       j <- forAll $ genVectorIndex (knownNat @10)
       (i == j) === (j == i)

  , testProperty "Eq-VectorIndex-transitive" $ property $
    do i <- forAll $ genVectorIndex (knownNat @10)
       j <- forAll $ genVectorIndex (knownNat @10)
       k <- forAll $ genVectorIndex (knownNat @10)
       (((i == j) && (j == k)) <= (i == k)) === True

  , testProperty "Ord-Eq-VectorIndex" $ property $
    do i <- forAll $ genVectorIndex (knownNat @10)
       j <- forAll $ genVectorIndex (knownNat @10)
       (i == j) === (compare i j == EQ)
  ]
