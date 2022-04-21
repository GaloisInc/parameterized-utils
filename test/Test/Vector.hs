{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE TypeApplications #-}
{-# Language CPP #-}
{-# Language DataKinds #-}
{-# Language ExplicitForAll #-}
{-# Language FlexibleInstances #-}
{-# Language LambdaCase #-}
{-# Language OverloadedStrings #-}
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
  , SomeVector(..)
  , genSomeVector
  , genVectorOfLength
  , genOrdering
  , orderingEndomorphisms
  , orderingToStringFuns
  )
where

import           Data.Functor.Const (Const(..))
import           Data.Functor.WithIndex (imap)
import           Data.Foldable.WithIndex (ifoldMap)
import           Data.Maybe (isJust)
import qualified Data.List as List
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Fin
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.Vector
import           Data.Semigroup
import           GHC.TypeLits (KnownNat)
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range
import           Numeric.Natural (Natural)
import           Prelude hiding (take, reverse, length)
import qualified Prelude as P
import           Test.Fin (genFin)
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Context (genSomePayloadList, mkUAsgn)

#if __GLASGOW_HASKELL__ >= 806
import qualified Hedgehog.Classes as HC
import           Test.Tasty.HUnit (assertBool, testCase)
#endif

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

instance Show (a -> b) where
  show _ = "unshowable"

-- Used to test e.g., 'fmap (g . f) = fmap g . fmap f' and 'imap (const f) =
-- fmap f'.
orderingEndomorphisms :: [Ordering -> Ordering]
orderingEndomorphisms =
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
  
-- | Used to test ifoldMap.
orderingToStringFuns :: [ Ordering -> String ]
orderingToStringFuns =
  [ const "s"
  , show
  ]

prop_reverse100 :: Property
prop_reverse100 = property $
  do SomeVector v <- forAll $ genSomeVector genOrdering
     case testLeq (knownNat @1) (length v) of
       Nothing -> pure ()
       Just LeqProof -> v === (reverse $ reverse v)

prop_reverseSingleton :: Property
prop_reverseSingleton = property $
  do l <- (:[]) <$> forAll genOrdering
     Just v <- return $ fromList (knownNat @1) l
     v === reverse v

prop_splitJoin :: Property
prop_splitJoin = property $
  do let n = knownNat @5
     v <- forAll $ genVectorKnownLength @(5 * 5) genOrdering
     v === (join n $ split n (knownNat @5) v)

prop_cons :: Property
prop_cons = property $
  do let n = knownNat @20
         w = widthVal n
     l <- forAll $ HG.list (constant w w) genOrdering
     x <- forAll genOrdering
     (cons x <$> fromList n l) === fromList (incNat n) (x:l)

prop_snoc :: Property
prop_snoc = property $
  do let n = knownNat @20
         w = widthVal n
     l <- forAll $ HG.list (constant w w) genOrdering
     x <- forAll genOrdering
     (flip snoc x <$> fromList n l) === fromList (incNat n) (l ++ [x])

prop_snocUnsnoc :: Property
prop_snocUnsnoc = property $
  do let n = knownNat @20
         w = widthVal n
     l <- forAll $ HG.list (constant w w) genOrdering
     x <- forAll genOrdering
     (fst  . unsnoc . flip snoc x <$> fromList n l) === Just x

prop_generate :: Property
prop_generate = property $
  do let n = knownNat @55
         w = widthVal n
         funs :: [ Int -> Ordering ]  -- some miscellaneous functions to generate Vector values
         funs =  [ const EQ
                 , \i -> if i < 10 then LT else if i > 15 then GT else EQ
                 , \i -> if i == 0 then EQ else GT
                 ]
     f <- forAll $ HG.element funs
     Just (generate n (f . widthVal)) === fromList (incNat n) (map f [0..w])

prop_unfold :: Property
prop_unfold = property $
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

prop_toFromAssignment :: Property
prop_toFromAssignment = property $
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

prop_fmapId :: Property
prop_fmapId = property $
  do SomeVector v <- forAll $ genSomeVector genOrdering
     fmap id v === v

prop_fmapCompose :: Property
prop_fmapCompose = property $
  do SomeVector v <- forAll $ genSomeVector genOrdering
     f <- forAll $ HG.element orderingEndomorphisms
     g <- forAll $ HG.element orderingEndomorphisms
     fmap (g . f) v === fmap g (fmap f v)

prop_iterateNRange :: Property
prop_iterateNRange = property $
  do Some len <- mkNatRepr <$> forAll (HG.integral (linear 0 (99 :: Natural)))
     toList (iterateN len (+1) 0) === [0..(natValue len)]

prop_indicesOfRange :: Property
prop_indicesOfRange = property $
  do SomeVector v <- forAll $ genSomeVector genOrdering
     toList (fmap (viewFin natValue) (indicesOf v)) === [0..(natValue (length v) - 1)]

prop_imapConst :: Property
prop_imapConst = property $
  do f <- forAll $ HG.element orderingEndomorphisms
     SomeVector v <- forAll $ genSomeVector genOrdering
     imap (const f) v === fmap f v

prop_ifoldMapConst :: Property
prop_ifoldMapConst = property $
  do let funs :: [ Ordering -> String ]
         funs = [const "s", show]
     f <- forAll $ HG.element funs
     SomeVector v <- forAll $ genSomeVector genOrdering
     ifoldMap (const f) v === foldMap f v

prop_imapConstIndicesOf :: Property
prop_imapConstIndicesOf = property $
  do SomeVector v <- forAll $ genSomeVector genOrdering
     imap const v === indicesOf v

prop_imapElemAt :: Property
prop_imapElemAt = property $
  do SomeVector v <- forAll $ genSomeVector genOrdering
     imap (\i _ -> viewFin (\x -> elemAt x v) i) v === v

prop_OrdEqVectorIndex :: Property
prop_OrdEqVectorIndex = property $
  do i <- forAll $ genFin (knownNat @10)
     j <- forAll $ genFin (knownNat @10)
     (i == j) === (compare i j == EQ)

-- We use @Ordering@ just because it's simple
vecTests :: IO TestTree
vecTests = testGroup "Vector" <$> return
  [ testPropertyNamed "reverse100" "prop_reverse100" prop_reverse100
  , testPropertyNamed "reverseSingleton" "prop_reverseSingleton" prop_reverseSingleton

  , testPropertyNamed "split-join" "prop_splitJoin" prop_splitJoin

  -- @cons@ is the same for vectors or lists
  , testPropertyNamed "cons" "prop_cons" prop_cons

  -- @snoc@ is like appending to a list
  , testPropertyNamed "snoc" "prop_snoc" prop_snoc

  -- @snoc@ and @unsnoc@ are inverses
  , testPropertyNamed "snoc/unsnoc" "prop_snocUnsnoc" prop_snocUnsnoc

  -- @generate@ is like mapping a function over indices
  , testPropertyNamed "generate" "prop_generate" prop_generate

  -- @unfold@ works like @unfold@ on lists
  , testPropertyNamed "unfold" "prop_unfold" prop_unfold

  -- Converting to and from assignments preserves size and last element
  , testPropertyNamed "to-from-assignment" "prop_toFromAssignment" prop_toFromAssignment

  -- NOTE: We don't use hedgehog-classes here, because the way the types work
  -- would require this to only tests vectors of some fixed size.
  --
  -- Also, for 'fmap-compose', hedgehog-classes only tests two fixed functions
  -- over integers.
  , testPropertyNamed "fmap-id" "prop_fmapId" prop_fmapId

  , testPropertyNamed "fmap-compose" "prop_fmapCompose" prop_fmapCompose

  , testPropertyNamed "iterateN-range" "prop_iterateNRange" prop_iterateNRange

  , testPropertyNamed "indicesOf-range" "prop_indicesOfRange" prop_indicesOfRange

  , testPropertyNamed "imap-const" "prop_imapConst" prop_imapConst

  , testPropertyNamed "ifoldMap-const" "prop_ifoldMapConst" prop_ifoldMapConst

  , testPropertyNamed "imap-const-indicesOf" "prop_imapConstIndicesOf" prop_imapConstIndicesOf

  , testPropertyNamed "imap-elemAt" "prop_imapElemAt" prop_imapElemAt

  , testPropertyNamed "Ord-Eq-VectorIndex" "prop_OrdEqVectorIndex" prop_OrdEqVectorIndex

#if __GLASGOW_HASKELL__ >= 806
  -- Test a few different sizes since the types force each test to use a
  -- specific size vector.
  , testCase "Eq-Vector-laws-1" $
      assertBool "Eq-Vector-laws-1" =<<
        HC.lawsCheck (HC.eqLaws (genVectorKnownLength @1 genOrdering))
  , testCase "Eq-Vector-laws-10" $
      assertBool "Eq-Vector-laws-10" =<<
        HC.lawsCheck (HC.eqLaws (genVectorKnownLength @10 genOrdering))
  , testCase "Show-Vector-laws-1" $
      assertBool "Show-Vector-laws-1" =<<
        HC.lawsCheck (HC.showLaws (genVectorKnownLength @1 genOrdering))
  , testCase "Show-Vector-laws-10" $
      assertBool "Show-Vector-laws-10" =<<
        HC.lawsCheck (HC.showLaws (genVectorKnownLength @10 genOrdering))
  , testCase "Foldable-Vector-laws-1" $
      assertBool "Foldable-Vector-laws-1" =<<
        HC.lawsCheck (HC.foldableLaws (genVectorKnownLength @1))
  , testCase "Foldable-Vector-laws-10" $
      assertBool "Foldable-Vector-laws-10" =<<
        HC.lawsCheck (HC.foldableLaws (genVectorKnownLength @10))
  , testCase "Traversable-Vector-laws-1" $
      assertBool "Traversable-Vector-laws-1" =<<
        HC.lawsCheck (HC.traversableLaws (genVectorKnownLength @1))
  , testCase "Traversable-Vector-laws-10" $
      assertBool "Traversable-Vector-laws-10" =<<
        HC.lawsCheck (HC.traversableLaws (genVectorKnownLength @10))
#endif
  ]
