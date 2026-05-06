{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Semantic correctness tests for SmallArrayF RULES.
--
-- Each property verifies that the LHS and RHS of a rule produce the
-- same result on random inputs.  The combinators are wrapped with
-- NOINLINE to prevent GHC from applying the very rules we are
-- testing -- we want to evaluate each side independently and compare.
--
-- These tests complement the inspection tests: inspection verifies
-- the rule fires, these verify it preserves meaning.

module Test.SmallArrayF.RulesSemantics (tests) where

import           Control.Monad.ST (runST)
import           Data.Functor.Identity (Identity(Identity, runIdentity))
import           Data.Kind (Type)
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context (Index)
import           Data.Parameterized.Classes (ShowF(showF))
import           Data.Parameterized.Some
import qualified Data.Parameterized.SmallArrayF as SAF
import           Data.Parameterized.SmallArrayF (SmallArrayF)
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.TraversableFC.WithIndex
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range (linear)
import qualified Test.Tasty as TT
import           Test.Tasty.Hedgehog

------------------------------------------------------------------------
-- Payload: a simple uniform wrapper around Ordering

newtype V (tp :: Type) = V Int
  deriving (Show, Eq)

instance ShowF V where
  showF (V n) = show n

------------------------------------------------------------------------
-- Generator

genSomeVList :: Gen [Some V]
genSomeVList = HG.list (linear 1 12) (Some . V <$> HG.int (linear (-100) 100))

mkArr :: [Some V] -> Some (SmallArrayF V)
mkArr vals =
  case go Ctx.empty vals of
    Some a -> Some (SAF.fromAssignment a)
  where
    go :: Ctx.Assignment V ctx -> [Some V] -> Some (Ctx.Assignment V)
    go acc []            = Some acc
    go acc (Some x : xs) = go (Ctx.extend acc x) xs

toList :: SmallArrayF V ctx -> [Int]
toList = foldrFC (\(V n) r -> n : r) []

------------------------------------------------------------------------
-- NOINLINE combinators to prevent rule firing during semantics tests.

-- Eta-expanded: GHC 9.0-9.2 can't unify the rank-N class methods with
-- these monomorphic signatures when written pointfree.
{-# NOINLINE myFmapFC #-}
myFmapFC :: (forall tp. f tp -> g tp) -> SmallArrayF f ctx -> SmallArrayF g ctx
myFmapFC h arr = fmapFC h arr

{-# NOINLINE myImapFC #-}
myImapFC :: (forall tp. Index ctx tp -> f tp -> g tp) -> SmallArrayF f ctx -> SmallArrayF g ctx
myImapFC h arr = imapFC h arr

{-# NOINLINE myTraverseFC #-}
myTraverseFC :: Applicative m => (forall tp. f tp -> m (g tp)) -> SmallArrayF f ctx -> m (SmallArrayF g ctx)
myTraverseFC h arr = traverseFC h arr

{-# NOINLINE myItraverseFC #-}
myItraverseFC :: Applicative m => (forall tp. Index ctx tp -> f tp -> m (g tp)) -> SmallArrayF f ctx -> m (SmallArrayF g ctx)
myItraverseFC h arr = itraverseFC h arr

{-# NOINLINE myZipWithMFC #-}
myZipWithMFC :: Applicative m => (forall tp. f tp -> g tp -> m (h tp)) -> SmallArrayF f ctx -> SmallArrayF g ctx -> m (SmallArrayF h ctx)
myZipWithMFC h a b = SAF.zipWithMFC h a b

{-# NOINLINE myFromAssignment #-}
myFromAssignment :: Ctx.Assignment f ctx -> SmallArrayF f ctx
myFromAssignment = SAF.fromAssignment

{-# NOINLINE myToAssignment #-}
myToAssignment :: SmallArrayF f ctx -> Ctx.Assignment f ctx
myToAssignment = SAF.toAssignment

{-# NOINLINE myGenerateA #-}
myGenerateA :: Applicative m => Ctx.Size ctx -> (forall tp. Index ctx tp -> m (f tp)) -> m (SmallArrayF f ctx)
myGenerateA = SAF.generateA

------------------------------------------------------------------------
-- Element-level functions

twiddle :: V tp -> V tp
twiddle (V n) = V (n + 1)

twaddle :: V tp -> V tp
twaddle (V n) = V (n * 2)

itwiddle :: Index ctx tp -> V tp -> V tp
itwiddle idx (V n) = V (n + Ctx.indexVal idx)

itwaddle :: Index ctx tp -> V tp -> V tp
itwaddle idx (V n) = V (n * (1 + Ctx.indexVal idx))

------------------------------------------------------------------------
-- Properties

prop_fmapFC_fmapFC :: Property
prop_fmapFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ myFmapFC twaddle (myFmapFC twiddle arr)
      rhs = toList $ myFmapFC (twaddle . twiddle) arr
  lhs === rhs

prop_traverseFC_fmapFC :: Property
prop_traverseFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ runIdentity $ myTraverseFC (Identity . twaddle) (myFmapFC twiddle arr)
      rhs = toList $ runIdentity $ myTraverseFC (Identity . twaddle . twiddle) arr
  lhs === rhs

prop_imapFC_fmapFC :: Property
prop_imapFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ myImapFC itwiddle (myFmapFC twiddle arr)
      rhs = toList $ myImapFC (\idx -> itwiddle idx . twiddle) arr
  lhs === rhs

prop_imapFC_imapFC :: Property
prop_imapFC_imapFC = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ myImapFC itwiddle (myImapFC itwaddle arr)
      rhs = toList $ myImapFC (\idx -> itwiddle idx . itwaddle idx) arr
  lhs === rhs

prop_fmapFC_imapFC :: Property
prop_fmapFC_imapFC = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ myFmapFC twaddle (myImapFC itwaddle arr)
      rhs = toList $ myImapFC (\idx -> twaddle . itwaddle idx) arr
  lhs === rhs

prop_itraverseFC_fmapFC :: Property
prop_itraverseFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ runIdentity $ myItraverseFC (\idx x -> Identity (itwiddle idx x)) (myFmapFC twiddle arr)
      rhs = toList $ runIdentity $ myItraverseFC (\idx -> Identity . itwiddle idx . twiddle) arr
  lhs === rhs

prop_itraverseFC_imapFC :: Property
prop_itraverseFC_imapFC = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ runIdentity $ myItraverseFC (\idx x -> Identity (itwiddle idx x)) (myImapFC itwaddle arr)
      rhs = toList $ runIdentity $ myItraverseFC (\idx -> Identity . itwiddle idx . itwaddle idx) arr
  lhs === rhs

prop_traverseFC_ST :: Property
prop_traverseFC_ST = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ runST $ myTraverseFC (\(V n) -> pure (V (n + 1))) arr
      rhs = toList $ runST $ SAF.traverseFCST (\(V n) -> pure (V (n + 1))) arr
  lhs === rhs

prop_traverseFC_IO :: Property
prop_traverseFC_IO = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  lhs <- evalIO $ fmap toList $ myTraverseFC (\(V n) -> pure (V (n + 1))) arr
  rhs <- evalIO $ fmap toList $ SAF.traverseFCIO (\(V n) -> pure (V (n + 1))) arr
  lhs === rhs

prop_itraverseFC_ST :: Property
prop_itraverseFC_ST = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ runST $ myItraverseFC (\idx (V n) -> pure (V (n + Ctx.indexVal idx))) arr
      rhs = toList $ runST $ SAF.itraverseFCST (\idx (V n) -> pure (V (n + Ctx.indexVal idx))) arr
  lhs === rhs

prop_itraverseFC_IO :: Property
prop_itraverseFC_IO = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  lhs <- evalIO $ fmap toList $ myItraverseFC (\idx (V n) -> pure (V (n + Ctx.indexVal idx))) arr
  rhs <- evalIO $ fmap toList $ SAF.itraverseFCIO (\idx (V n) -> pure (V (n + Ctx.indexVal idx))) arr
  lhs === rhs

prop_zipWithMFC_ST :: Property
prop_zipWithMFC_ST = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ runST $ myZipWithMFC (\(V a) (V b) -> pure (V (a + b))) arr arr
      rhs = toList $ runST $ SAF.zipWithMFCST (\(V a) (V b) -> pure (V (a + b))) arr arr
  lhs === rhs

prop_zipWithMFC_IO :: Property
prop_zipWithMFC_IO = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  lhs <- evalIO $ fmap toList $ myZipWithMFC (\(V a) (V b) -> pure (V (a + b))) arr arr
  rhs <- evalIO $ fmap toList $ SAF.zipWithMFCIO (\(V a) (V b) -> pure (V (a + b))) arr arr
  lhs === rhs

prop_fromTo :: Property
prop_fromTo = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let lhs = toList $ myFromAssignment (myToAssignment arr)
  lhs === toList arr

prop_toFrom :: Property
prop_toFrom = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  let asgn = myToAssignment arr
      lhs  = myToAssignment (myFromAssignment asgn)
  toListFC (\(V n) -> n) lhs === toListFC (\(V n) -> n) asgn

prop_generateA_Identity :: Property
prop_generateA_Identity = property $ do
  vals <- forAll genSomeVList
  Some (arr :: SmallArrayF V ctx) <- pure $ mkArr vals
  let fn :: forall tp. Index ctx tp -> Identity (V tp)
      fn idx = Identity (arr SAF.! idx)
      lhs = runIdentity $ myGenerateA (SAF.size arr) fn
      rhs = runIdentity $ Identity (SAF.generate (SAF.size arr) (runIdentity . fn))
  toList lhs === toList rhs

prop_fmapFC_id :: Property
prop_fmapFC_id = property $ do
  vals <- forAll genSomeVList
  Some arr <- pure $ mkArr vals
  toList (myFmapFC (\x -> x) arr) === toList arr

prop_takeAppend :: Property
prop_takeAppend = property $ do
  xs <- forAll genSomeVList
  ys <- forAll genSomeVList
  Some a <- pure $ mkArr xs
  Some b <- pure $ mkArr ys
  let combined = SAF.append a b
      lhs = toList $ SAF.take (SAF.size a) (SAF.size b) combined
  lhs === toList a

prop_dropAppend :: Property
prop_dropAppend = property $ do
  xs <- forAll genSomeVList
  ys <- forAll genSomeVList
  Some a <- pure $ mkArr xs
  Some b <- pure $ mkArr ys
  let combined = SAF.append a b
      lhs = toList $ SAF.drop (SAF.size a) (SAF.size b) combined
  lhs === toList b

------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "SmallArrayF RULES (semantics)"
  [ testPropertyNamed "fmapFC_/fmapFC_" "prop_fmapFC_fmapFC" prop_fmapFC_fmapFC
  , testPropertyNamed "traverseFC/fmapFC_" "prop_traverseFC_fmapFC" prop_traverseFC_fmapFC
  , testPropertyNamed "imapFC_/fmapFC_" "prop_imapFC_fmapFC" prop_imapFC_fmapFC
  , testPropertyNamed "imapFC_/imapFC_" "prop_imapFC_imapFC" prop_imapFC_imapFC
  , testPropertyNamed "fmapFC_/imapFC_" "prop_fmapFC_imapFC" prop_fmapFC_imapFC
  , testPropertyNamed "itraverseFC/fmapFC_" "prop_itraverseFC_fmapFC" prop_itraverseFC_fmapFC
  , testPropertyNamed "itraverseFC/imapFC_" "prop_itraverseFC_imapFC" prop_itraverseFC_imapFC
  , testPropertyNamed "traverseFC/ST" "prop_traverseFC_ST" prop_traverseFC_ST
  , testPropertyNamed "traverseFC/IO" "prop_traverseFC_IO" prop_traverseFC_IO
  , testPropertyNamed "itraverseFC/ST" "prop_itraverseFC_ST" prop_itraverseFC_ST
  , testPropertyNamed "itraverseFC/IO" "prop_itraverseFC_IO" prop_itraverseFC_IO
  , testPropertyNamed "zipWithMFC/ST" "prop_zipWithMFC_ST" prop_zipWithMFC_ST
  , testPropertyNamed "zipWithMFC/IO" "prop_zipWithMFC_IO" prop_zipWithMFC_IO
  , testPropertyNamed "fromAssignment/toAssignment" "prop_fromTo" prop_fromTo
  , testPropertyNamed "toAssignment/fromAssignment" "prop_toFrom" prop_toFrom
  , testPropertyNamed "generateA/Identity" "prop_generateA_Identity" prop_generateA_Identity
  , testPropertyNamed "fmapFC_/id" "prop_fmapFC_id" prop_fmapFC_id
  , testPropertyNamed "take/append" "prop_takeAppend" prop_takeAppend
  , testPropertyNamed "drop/append" "prop_dropAppend" prop_dropAppend
  ]
