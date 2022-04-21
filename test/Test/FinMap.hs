{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}


module Test.FinMap
  ( finMapTests
  )
where

import           Data.Proxy (Proxy(Proxy))
import           Data.Type.Equality ((:~:)(Refl))

import           Data.Parameterized.Fin (Fin)
import qualified Data.Parameterized.Fin as Fin
import           Data.Parameterized.NatRepr (LeqProof, NatRepr, type (<=), type (+))
import qualified Data.Parameterized.NatRepr as NatRepr

import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog

import qualified Data.Parameterized.FinMap.Safe as S
import qualified Data.Parameterized.FinMap.Unsafe as U

import           Test.Fin (genFin)
import           Test.Vector (SomeVector(..), genSomeVector, genOrdering)

data SomeSafeFinMap a = forall n. SomeSafeFinMap (S.FinMap n a)
data SomeUnsafeFinMap a = forall n. SomeUnsafeFinMap (U.FinMap n a)

instance Show a => Show (SomeSafeFinMap a) where
  show (SomeSafeFinMap v) = show v
instance Show a => Show (SomeUnsafeFinMap a) where
  show (SomeUnsafeFinMap v) = show v

genSomeSafeFinMap :: (Monad m) => GenT m a -> GenT m (SomeSafeFinMap a)
genSomeSafeFinMap genElem =
  do SomeVector v <- genSomeVector genElem
     return (SomeSafeFinMap (S.fromVector v))

genSomeUnsafeFinMap :: (Monad m) => GenT m a -> GenT m (SomeUnsafeFinMap a)
genSomeUnsafeFinMap genElem =
  do SomeVector v <- genSomeVector genElem
     return (SomeUnsafeFinMap (U.fromVector v))

prop_incMax_size_safe :: Property
prop_incMax_size_safe = property $
  do SomeSafeFinMap sm <- forAll $ genSomeSafeFinMap genOrdering
     Fin.finToNat (S.size (S.incMax sm)) === Fin.finToNat (S.size sm)

prop_incMax_size_unsafe :: Property
prop_incMax_size_unsafe = property $
  do SomeUnsafeFinMap sm <- forAll $ genSomeUnsafeFinMap genOrdering
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

prop_insert_size_safe :: Property
prop_insert_size_safe = property $
  do SomeSafeFinMap sm <- forAll $ genSomeSafeFinMap genOrdering
     withSizeSafe sm $ \i -> do
      idx <- forAll (genFin i)
      o <- forAll genOrdering
      let size = Fin.finToNat (S.size sm)
      let newSize = Fin.finToNat (S.size (S.insert (Fin.embed idx) o sm))
      assert (size == newSize || size + 1 == newSize)

prop_insert_size_unsafe :: Property
prop_insert_size_unsafe = property $
  do SomeUnsafeFinMap sm <- forAll $ genSomeUnsafeFinMap genOrdering
     withSizeUnsafe sm $ \i -> do
      idx <- forAll (genFin i)
      o <- forAll genOrdering
      let size = Fin.finToNat (U.size sm)
      let newSize = Fin.finToNat (U.size (U.insert (Fin.embed idx) o sm))
      assert (size == newSize || size + 1 == newSize)

prop_insert_delete_safe :: Property
prop_insert_delete_safe = property $
  do SomeSafeFinMap sm <- forAll $ genSomeSafeFinMap genOrdering
     withSizeSafe sm $ \i -> do
      idx <- Fin.embed <$> forAll (genFin i)
      o <- forAll genOrdering
      S.delete idx (S.insert idx o sm) === S.delete idx sm

prop_insert_delete_unsafe :: Property
prop_insert_delete_unsafe = property $
  do SomeUnsafeFinMap sm <- forAll $ genSomeUnsafeFinMap genOrdering
     withSizeUnsafe sm $ \i -> do
      idx <- Fin.embed <$> forAll (genFin i)
      o <- forAll genOrdering
      U.delete idx (U.insert idx o sm) === U.delete idx sm

prop_delete_insert_safe :: Property
prop_delete_insert_safe = property $
  do SomeSafeFinMap sm <- forAll $ genSomeSafeFinMap genOrdering
     withSizeSafe sm $ \i -> do
      idx <- Fin.embed <$> forAll (genFin i)
      o <- forAll genOrdering
      S.insert idx o (S.delete idx sm) === S.insert idx o sm

prop_delete_insert_unsafe :: Property
prop_delete_insert_unsafe = property $
  do SomeUnsafeFinMap sm <- forAll $ genSomeUnsafeFinMap genOrdering
     withSizeUnsafe sm $ \i -> do
      idx <- Fin.embed <$> forAll (genFin i)
      o <- forAll genOrdering
      U.insert idx o (U.delete idx sm) === U.insert idx o sm

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
  ]
