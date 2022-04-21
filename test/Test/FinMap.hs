{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}


module Test.FinMap
where

import           Control.Monad (foldM)
import           Data.Foldable.WithIndex (itoList)
import           Data.Proxy (Proxy(Proxy))
import           Data.Type.Equality ((:~:)(Refl))

import           Data.Parameterized.Fin (Fin)
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.NatRepr (LeqProof, NatRepr, type (<=), type (+))
import qualified Data.Parameterized.NatRepr as NatRepr

import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range (linear)
import           Test.Tasty
import           Test.Tasty.Hedgehog

#if __GLASGOW_HASKELL__ >= 806
import           Test.Tasty.HUnit (assertBool, testCase)
import qualified Hedgehog.Classes as HC
#endif

import qualified Data.Parameterized.FinMap.Safe as S
import qualified Data.Parameterized.FinMap.Unsafe as U
import qualified Data.Parameterized.Vector as Vec

import           Test.Fin (genFin)
import           Test.Vector (SomeVector(..), genSomeVector, genVectorOfLength, genOrdering)

data SomeSafeFinMap a = forall n. SomeSafeFinMap (NatRepr n) (S.FinMap n a)
data SomeUnsafeFinMap a = forall n. SomeUnsafeFinMap (NatRepr n) (U.FinMap n a)

instance Show a => Show (SomeSafeFinMap a) where
  show (SomeSafeFinMap _ v) = show v
instance Show a => Show (SomeUnsafeFinMap a) where
  show (SomeUnsafeFinMap _ v) = show v

genSafeFinMap :: (Monad m) => NatRepr n -> GenT m a -> GenT m (S.FinMap (n + 1) a)
genSafeFinMap n genElem = S.fromVector <$> genVectorOfLength n genElem

genUnsafeFinMap :: (Monad m) => NatRepr n -> GenT m a -> GenT m (U.FinMap (n + 1) a)
genUnsafeFinMap n genElem = U.fromVector <$> genVectorOfLength n genElem

genSomeSafeFinMap :: (Monad m) => GenT m a -> GenT m (SomeSafeFinMap a)
genSomeSafeFinMap genElem =
  do SomeVector v <- genSomeVector genElem
     return (SomeSafeFinMap (Vec.length v) (S.fromVector v))

genSomeUnsafeFinMap :: (Monad m) => GenT m a -> GenT m (SomeUnsafeFinMap a)
genSomeUnsafeFinMap genElem =
  do SomeVector v <- genSomeVector genElem
     return (SomeUnsafeFinMap (Vec.length v) (U.fromVector v))

prop_incMax_size_safe :: Property
prop_incMax_size_safe = property $
  do SomeSafeFinMap _ sm <- forAll $ genSomeSafeFinMap genOrdering
     Fin.finToNat (S.size (S.incMax sm)) === Fin.finToNat (S.size sm)

prop_incMax_size_unsafe :: Property
prop_incMax_size_unsafe = property $
  do SomeUnsafeFinMap _ sm <- forAll $ genSomeUnsafeFinMap genOrdering
     Fin.finToNat (U.size (U.incMax sm)) === Fin.finToNat (U.size sm)

cancelPlusOne ::
  forall f g i n.
  f i ->
  g n ->
  LeqProof (i + 1) (n + 1) ->
  LeqProof i n
cancelPlusOne i n NatRepr.LeqProof =
  case NatRepr.plusMinusCancel n (NatRepr.knownNat :: NatRepr 1) of
    Refl ->
      case NatRepr.plusMinusCancel i (NatRepr.knownNat :: NatRepr 1) of
        Refl ->
          case NatRepr.leqSub2
                  (NatRepr.LeqProof :: LeqProof (i + 1) (n + 1))
                  (NatRepr.LeqProof :: LeqProof 1 1) of
            NatRepr.LeqProof -> NatRepr.LeqProof

withSizeSafe ::
  S.FinMap n a ->
  (forall i. (i + 1 <= n + 1, i <= n) => NatRepr i -> r) ->
  r
withSizeSafe sm k =
  case S.size sm of
    (sz :: Fin (n + 1)) ->
      Fin.viewFin
        (\(i :: NatRepr i) ->
          case cancelPlusOne i (Proxy :: Proxy n) NatRepr.LeqProof of
            NatRepr.LeqProof -> k i)
        sz

withIndexSafe ::
  SomeSafeFinMap a ->
  (forall n. Fin n -> S.FinMap n a -> PropertyT IO ()) ->
  PropertyT IO ()
withIndexSafe (SomeSafeFinMap n sm) k =
  case NatRepr.isZeroOrGT1 n of
    Left Refl -> k Fin.minFin (S.incMax sm)
    Right NatRepr.LeqProof ->
      do idx <- forAll (genFin n)
         k idx sm

withSizeUnsafe ::
  U.FinMap n a ->
  (forall i. (i + 1 <= n + 1, i <= n) => NatRepr i -> r) ->
  r
withSizeUnsafe sm k =
  case U.size sm of
    (sz :: Fin (n + 1)) ->
      Fin.viewFin
        (\(i :: NatRepr i) ->
          case cancelPlusOne i (Proxy :: Proxy n) NatRepr.LeqProof of
            NatRepr.LeqProof -> k i)
        sz

withIndexUnsafe ::
  SomeUnsafeFinMap a ->
  (forall n. Fin n -> U.FinMap n a -> PropertyT IO ()) ->
  PropertyT IO ()
withIndexUnsafe (SomeUnsafeFinMap n sm) k =
  case NatRepr.isZeroOrGT1 n of
    Left Refl -> k Fin.minFin (U.incMax sm)
    Right NatRepr.LeqProof ->
      do idx <- forAll (genFin n)
         k idx sm

prop_insert_size_safe :: Property
prop_insert_size_safe = property $
  do ssm <- forAll $ genSomeSafeFinMap genOrdering
     withIndexSafe ssm $ \idx sm -> do
      o <- forAll genOrdering
      let size = Fin.finToNat (S.size sm)
      let newSize = Fin.finToNat (S.size (S.insert (Fin.embed idx) o sm))
      assert (size == newSize || size + 1 == newSize)

prop_insert_size_unsafe :: Property
prop_insert_size_unsafe = property $
  do ssm <- forAll $ genSomeUnsafeFinMap genOrdering
     withIndexUnsafe ssm $ \idx sm -> do
      o <- forAll genOrdering
      let size = Fin.finToNat (U.size sm)
      let newSize = Fin.finToNat (U.size (U.insert (Fin.embed idx) o sm))
      assert (size == newSize || size + 1 == newSize)

prop_insert_delete_safe :: Property
prop_insert_delete_safe = property $
  do ssm <- forAll $ genSomeSafeFinMap genOrdering
     withIndexSafe ssm $ \idx sm -> do
      o <- forAll genOrdering
      S.delete idx (S.insert idx o sm) === S.delete idx sm

prop_insert_delete_unsafe :: Property
prop_insert_delete_unsafe = property $
  do ssm <- forAll $ genSomeUnsafeFinMap genOrdering
     withIndexUnsafe ssm $ \idx sm -> do
      o <- forAll genOrdering
      U.delete idx (U.insert idx o sm) === U.delete idx sm

prop_delete_insert_safe :: Property
prop_delete_insert_safe = property $
  do ssm <- forAll $ genSomeSafeFinMap genOrdering
     withIndexSafe ssm $ \idx sm -> do
      o <- forAll genOrdering
      S.insert idx o (S.delete idx sm) === S.insert idx o sm

prop_delete_insert_unsafe :: Property
prop_delete_insert_unsafe = property $
  do ssm <- forAll $ genSomeUnsafeFinMap genOrdering
     withIndexUnsafe ssm $ \idx sm -> do
      o <- forAll genOrdering
      U.insert idx o (U.delete idx sm) === U.insert idx o sm

prop_empty_insert_safe :: Property
prop_empty_insert_safe = property $
  do withIndexSafe (SomeSafeFinMap NatRepr.knownNat S.empty) $ \idx sm -> do
      o <- forAll genOrdering
      sm /== S.insert idx o sm

prop_empty_insert_unsafe :: Property
prop_empty_insert_unsafe = property $
  do withIndexUnsafe (SomeUnsafeFinMap NatRepr.knownNat U.empty) $ \idx sm -> do
      o <- forAll genOrdering
      sm /== U.insert idx o sm

-- | Type used for comparative API tests
data MatchedMaps a =
  forall n.
  MatchedMaps
    { _unsafe :: U.FinMap n a
    , _safe :: S.FinMap n a
    }

operations :: Show a => Gen a -> [MatchedMaps a -> PropertyT IO (MatchedMaps a)]
operations genValue =
  [
    \(MatchedMaps u s) ->
      withSizeUnsafe u $ \sz -> do
        case NatRepr.isZeroOrGT1 sz of
          Left Refl ->
            do v <- forAll genValue
               return $
                 MatchedMaps
                   (U.insert Fin.minFin v (U.incMax u))
                   (S.insert Fin.minFin v (S.incMax s))
          Right NatRepr.LeqProof ->
            do idx <- Fin.embed <$> forAll (genFin sz)
               v <- forAll genValue
               return (MatchedMaps (U.insert idx v u) (S.insert idx v s))
  , \(MatchedMaps u s) ->
        return (MatchedMaps (U.incMax u) (S.incMax s))
  , \(MatchedMaps _ _) ->
        return (MatchedMaps U.empty S.empty)
  ]

-- | Possibly the most important and far-reaching test: The unsafe API should
-- yield the same results as the safe API, after some randomized sequence of
-- operations.
prop_safe_unsafe :: Property
prop_safe_unsafe = property $
  do numOps <- forAll (HG.integral (linear 0 (99 :: Int)))
     let empty = MatchedMaps U.empty S.empty
     MatchedMaps u s <-
       doTimes (chooseAndApply (operations genOrdering)) numOps empty
     itoList u === itoList s
  where
    chooseAndApply :: [a -> PropertyT IO b] -> a -> PropertyT IO b
    chooseAndApply funs arg =
      do f <- forAll $ HG.choice (map return funs)
         f arg

    doTimes f n m =
      foldM (\accum () -> f accum) m (take n (repeat ()))


finMapTests :: IO TestTree
finMapTests = testGroup "FinMap" <$> return
  [ testPropertyNamed "incSize-decSize-safe" "prop_incMax_size_safe" prop_incMax_size_safe
  , testPropertyNamed "incSize-decSize-unsafe" "prop_incMax_size_unsafe" prop_incMax_size_unsafe
  , testPropertyNamed "insert-size-safe" "prop_insert_size_safe" prop_insert_size_safe
  , testPropertyNamed "insert-size-unsafe" "prop_insert_size_unsafe" prop_insert_size_unsafe
  , testPropertyNamed "insert-delete-safe" "prop_insert_delete_safe" prop_insert_delete_safe
  , testPropertyNamed "insert-delete-unsafe" "prop_insert_delete_unsafe" prop_insert_delete_unsafe
  , testPropertyNamed "delete-insert-safe" "prop_delete_insert_safe" prop_delete_insert_safe
  , testPropertyNamed "delete-insert-unsafe" "prop_delete_insert_unsafe" prop_delete_insert_unsafe
  , testPropertyNamed "empty-insert-safe" "prop_empty_insert_safe" prop_empty_insert_safe
  , testPropertyNamed "empty-insert-unsafe" "prop_empty_insert_unsafe" prop_empty_insert_unsafe
  , testPropertyNamed "safe-unsafe" "prop_safe_unsafe" prop_safe_unsafe

#if __GLASGOW_HASKELL__ >= 806
  , testCase "Eq-Safe-FinMap-laws-1" $
      assertBool "Eq-Safe-FinMap-laws-1" =<<
        HC.lawsCheck (HC.eqLaws (genSafeFinMap (NatRepr.knownNat @1) genOrdering))
  , testCase "Eq-Unsafe-FinMap-laws-1" $
      assertBool "Eq-Unsafe-FinMap-laws-1" =<<
        HC.lawsCheck (HC.eqLaws (genUnsafeFinMap (NatRepr.knownNat @1) genOrdering))
  , testCase "Eq-Safe-FinMap-laws-10" $
      assertBool "Eq-Safe-FinMap-laws-1" =<<
        HC.lawsCheck (HC.eqLaws (genSafeFinMap (NatRepr.knownNat @10) genOrdering))
  , testCase "Eq-Unsafe-FinMap-laws-10" $
      assertBool "Eq-Unsafe-FinMap-laws-1" =<<
        HC.lawsCheck (HC.eqLaws (genUnsafeFinMap (NatRepr.knownNat @10) genOrdering))
  , testCase "Foldable-Safe-FinMap-laws-1" $
      assertBool "Foldable-Safe-FinMap-laws-1" =<<
        HC.lawsCheck (HC.foldableLaws (genSafeFinMap (NatRepr.knownNat @1)))
  , testCase "Foldable-Unsafe-FinMap-laws-1" $
      assertBool "Foldable-Unsafe-FinMap-laws-1" =<<
        HC.lawsCheck (HC.foldableLaws (genUnsafeFinMap (NatRepr.knownNat @1)))
  , testCase "Foldable-Safe-FinMap-laws-10" $
      assertBool "Foldable-Safe-FinMap-laws-10" =<<
        HC.lawsCheck (HC.foldableLaws (genSafeFinMap (NatRepr.knownNat @10)))
  , testCase "Foldable-Unsafe-FinMap-laws-10" $
      assertBool "Foldable-Unsafe-FinMap-laws-10" =<<
        HC.lawsCheck (HC.foldableLaws (genUnsafeFinMap (NatRepr.knownNat @10)))
#endif
  ]
