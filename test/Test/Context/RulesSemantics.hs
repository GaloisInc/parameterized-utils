{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Semantic correctness tests for Assignment RULES.
--
-- Each property verifies that the LHS and RHS of a rule produce the
-- same result on random inputs.  The combinators are wrapped with
-- NOINLINE to prevent GHC from applying the very rules we are
-- testing — we want to evaluate each side independently and compare.
--
-- These tests complement the inspection tests in Rules.hs:
-- inspection verifies the rule fires; these verify it preserves meaning.

module Test.Context.RulesSemantics (tests) where

import           Data.Functor.Identity (Identity(Identity, runIdentity))
import           Data.Kind (Type)
import qualified Data.Parameterized.Context as C
import           Data.Parameterized.Context (Index)
import           Data.Parameterized.Classes (ShowF(showF))
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.TraversableFC.WithIndex
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range (linear)
import qualified Test.Tasty as TT
import           Test.Tasty.Hedgehog

------------------------------------------------------------------------
-- Payload

newtype V (tp :: Type) = V Int
  deriving (Show, Eq)

unV :: V tp -> Int
unV (V n) = n

instance ShowF V where
  showF (V n) = show n


------------------------------------------------------------------------
-- Generator

genSomeVList :: Gen [Some V]
genSomeVList = HG.list (linear 1 12) (Some . V <$> HG.int (linear (-100) 100))

mkAsgn :: [Some V] -> Some (C.Assignment V)
mkAsgn = go C.empty
  where
    go :: C.Assignment V ctx -> [Some V] -> Some (C.Assignment V)
    go acc []            = Some acc
    go acc (Some x : xs) = go (C.extend acc x) xs

toList :: C.Assignment V ctx -> [Int]
toList = toListFC (\(V n) -> n)

------------------------------------------------------------------------
-- NOINLINE wrappers to prevent rule firing during semantics tests.

{-# NOINLINE myFmapFC #-}
myFmapFC :: (forall tp. f tp -> g tp) -> C.Assignment f ctx -> C.Assignment g ctx
myFmapFC f x = fmapFC f x

{-# NOINLINE myImapFC #-}
myImapFC :: (forall tp. Index ctx tp -> f tp -> g tp) -> C.Assignment f ctx -> C.Assignment g ctx
myImapFC f x = imapFC f x

{-# NOINLINE myTraverseFC #-}
myTraverseFC :: Applicative m => (forall tp. f tp -> m (g tp)) -> C.Assignment f ctx -> m (C.Assignment g ctx)
myTraverseFC f x = traverseFC f x

{-# NOINLINE myTraverseWithIndex #-}
myTraverseWithIndex :: Applicative m => (forall tp. Index ctx tp -> f tp -> m (g tp)) -> C.Assignment f ctx -> m (C.Assignment g ctx)
myTraverseWithIndex f x = C.traverseWithIndex f x

{-# NOINLINE myGenerate #-}
myGenerate :: C.Size ctx -> (forall tp. Index ctx tp -> f tp) -> C.Assignment f ctx
myGenerate = C.generate

{-# NOINLINE myIndex #-}
myIndex :: C.Assignment f ctx -> Index ctx tp -> f tp
myIndex = (C.!)

{-# NOINLINE myZipWithM #-}
myZipWithM :: Applicative m
           => (forall tp. f tp -> g tp -> m (h tp))
           -> C.Assignment f ctx -> C.Assignment g ctx -> m (C.Assignment h ctx)
myZipWithM = C.zipWithM

{-# NOINLINE myGenerateM #-}
myGenerateM :: Applicative m => C.Size ctx -> (forall tp. Index ctx tp -> m (f tp)) -> m (C.Assignment f ctx)
myGenerateM = C.generateM



------------------------------------------------------------------------
-- Element-level functions

twiddle :: V tp -> V tp
twiddle (V n) = V (n + 1)

twaddle :: V tp -> V tp
twaddle (V n) = V (n * 2)

itwiddle :: Index ctx tp -> V tp -> V tp
itwiddle idx (V n) = V (n + C.indexVal idx)

itwaddle :: Index ctx tp -> V tp -> V tp
itwaddle idx (V n) = V (n * (1 + C.indexVal idx))

------------------------------------------------------------------------
-- Properties
-- Test names exactly match RULE names.

prop_fmapFC_id :: Property
prop_fmapFC_id = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  toList (myFmapFC (\x -> x) asgn) === toList asgn

prop_fmapFC_fmapFC :: Property
prop_fmapFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ myFmapFC twaddle (myFmapFC twiddle asgn)
      rhs = toList $ myFmapFC (twaddle . twiddle) asgn
  lhs === rhs

prop_traverseFC_fmapFC :: Property
prop_traverseFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ runIdentity $ myTraverseFC (Identity . twaddle) (myFmapFC twiddle asgn)
      rhs = toList $ runIdentity $ myTraverseFC (Identity . twaddle . twiddle) asgn
  lhs === rhs

prop_traverseFC_imapFC :: Property
prop_traverseFC_imapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ runIdentity $ myTraverseFC (Identity . twaddle) (myImapFC itwaddle asgn)
      rhs = toList $ runIdentity $ myTraverseWithIndex (\idx -> Identity . twaddle . itwaddle idx) asgn
  lhs === rhs

prop_itraverseFC_fmapFC :: Property
prop_itraverseFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ runIdentity $
              myTraverseWithIndex (\idx x -> Identity (itwiddle idx x)) (myFmapFC twiddle asgn)
      rhs = toList $ runIdentity $
              myTraverseWithIndex (\idx -> Identity . itwiddle idx . twiddle) asgn
  lhs === rhs

prop_itraverseFC_imapFC :: Property
prop_itraverseFC_imapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ runIdentity $
              myTraverseWithIndex (\idx x -> Identity (itwiddle idx x)) (myImapFC itwaddle asgn)
      rhs = toList $ runIdentity $
              myTraverseWithIndex (\idx -> Identity . itwiddle idx . itwaddle idx) asgn
  lhs === rhs

prop_imapFC_fmapFC :: Property
prop_imapFC_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ myImapFC itwiddle (myFmapFC twiddle asgn)
      rhs = toList $ myImapFC (\idx -> itwiddle idx . twiddle) asgn
  lhs === rhs

prop_imapFC_imapFC :: Property
prop_imapFC_imapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ myImapFC itwiddle (myImapFC itwaddle asgn)
      rhs = toList $ myImapFC (\idx -> itwiddle idx . itwaddle idx) asgn
  lhs === rhs

prop_fmapFC_imapFC :: Property
prop_fmapFC_imapFC = property $ do
  vals <- forAll genSomeVList
  Some asgn <- pure $ mkAsgn vals
  let lhs = toList $ myFmapFC twaddle (myImapFC itwaddle asgn)
      rhs = toList $ myImapFC (\idx -> twaddle . itwaddle idx) asgn
  lhs === rhs

prop_fmapFC_generate :: Property
prop_fmapFC_generate = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  let n = C.size asgn
      g :: forall tp. Index ctx tp -> V tp
      g idx = asgn C.! idx
      lhs = toList $ myFmapFC twiddle (myGenerate n g)
      rhs = toList $ myGenerate n (\idx -> twiddle (g idx))
  lhs === rhs

prop_imapFC_generate :: Property
prop_imapFC_generate = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  let n = C.size asgn
      g :: forall tp. Index ctx tp -> V tp
      g idx = asgn C.! idx
      lhs = toList $ myImapFC itwiddle (myGenerate n g)
      rhs = toList $ myGenerate n (\idx -> itwiddle idx (g idx))
  lhs === rhs

prop_index_fmapFC :: Property
prop_index_fmapFC = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  case C.viewAssign asgn of
    C.AssignEmpty -> success
    C.AssignExtend _ _ -> do
      let idx = C.lastIndex (C.size asgn)
          V lhs = myIndex (myFmapFC twiddle asgn) idx
          V rhs = twiddle (myIndex asgn idx)
      lhs === rhs

prop_index_imapFC :: Property
prop_index_imapFC = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  case C.viewAssign asgn of
    C.AssignEmpty -> success
    C.AssignExtend _ _ -> do
      let idx = C.lastIndex (C.size asgn)
          V lhs = myIndex (myImapFC itwiddle asgn) idx
          V rhs = itwiddle idx (myIndex asgn idx)
      lhs === rhs

prop_index_generate :: Property
prop_index_generate = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  case C.viewAssign asgn of
    C.AssignEmpty -> success
    C.AssignExtend _ _ -> do
      let n = C.size asgn
          g :: forall tp. Index ctx tp -> V tp
          g i = asgn C.! i
          lastIdx = C.lastIndex n
          V lhs = myIndex (myGenerate n g) lastIdx
          V rhs = g lastIdx
      lhs === rhs

prop_traverseFC_generate :: Property
prop_traverseFC_generate = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  let n = C.size asgn
      g :: forall tp. Index ctx tp -> V tp
      g idx = asgn C.! idx
      lhs = toList $ runIdentity $ myTraverseFC (Identity . twiddle) (myGenerate n g)
      rhs = toList $ runIdentity $ myGenerateM n (Identity . twiddle . g)
  lhs === rhs

prop_traverseWithIndex_generate :: Property
prop_traverseWithIndex_generate = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  let n = C.size asgn
      g :: forall tp. Index ctx tp -> V tp
      g idx = asgn C.! idx
      lhs = toList $ runIdentity $ myTraverseWithIndex (\idx x -> Identity (itwiddle idx x)) (myGenerate n g)
      rhs = toList $ runIdentity $ myGenerateM n (\idx -> Identity (itwiddle idx (g idx)))
  lhs === rhs

prop_zipWithM_fmapFC_l :: Property
prop_zipWithM_fmapFC_l = property $ do
  vals1 <- forAll genSomeVList
  Some (asgn1 :: C.Assignment V ctx) <- pure $ mkAsgn vals1
  let n = C.size asgn1
      g :: forall tp. Index ctx tp -> V tp
      g idx = asgn1 C.! idx
      asgn2 = myGenerate n g
      lhs = toList $ runIdentity $
              myZipWithM (\x y -> Identity (V (unV x + unV y))) (myFmapFC twiddle asgn1) asgn2
      rhs = toList $ runIdentity $
              myZipWithM (\x y -> Identity (V (unV (twiddle x) + unV y))) asgn1 asgn2
  lhs === rhs

prop_zipWithM_fmapFC_r :: Property
prop_zipWithM_fmapFC_r = property $ do
  vals1 <- forAll genSomeVList
  Some (asgn1 :: C.Assignment V ctx) <- pure $ mkAsgn vals1
  let n = C.size asgn1
      g :: forall tp. Index ctx tp -> V tp
      g idx = asgn1 C.! idx
      asgn2 = myGenerate n g
      lhs = toList $ runIdentity $
              myZipWithM (\x y -> Identity (V (unV x + unV y))) asgn1 (myFmapFC twiddle asgn2)
      rhs = toList $ runIdentity $
              myZipWithM (\x y -> Identity (V (unV x + unV (twiddle y)))) asgn1 asgn2
  lhs === rhs


prop_fmapFC_traverseFC :: Property
prop_fmapFC_traverseFC = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  let fn :: forall tp. V tp -> Identity (V tp)
      fn = Identity . twiddle
      lhs = toList $ runIdentity $ fmap (myFmapFC twaddle) (myTraverseFC fn asgn)
      rhs = toList $ runIdentity $ myTraverseFC (fmap twaddle . fn) asgn
  lhs === rhs

prop_zipWithM_generate_l :: Property
prop_zipWithM_generate_l = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  let n = C.size asgn
      fn :: forall tp. Index ctx tp -> V tp
      fn idx = twiddle (asgn C.! idx)
      lhs = toList $ runIdentity $
              myZipWithM (\x y -> Identity (V (unV x + unV y))) (myGenerate n fn) asgn
      rhs = toList $ runIdentity $
              myGenerateM n (\idx -> Identity (V (unV (fn idx) + unV (asgn C.! idx))))
  lhs === rhs

prop_zipWithM_generate_r :: Property
prop_zipWithM_generate_r = property $ do
  vals <- forAll genSomeVList
  Some (asgn :: C.Assignment V ctx) <- pure $ mkAsgn vals
  let n = C.size asgn
      fn :: forall tp. Index ctx tp -> V tp
      fn idx = twiddle (asgn C.! idx)
      lhs = toList $ runIdentity $
              myZipWithM (\x y -> Identity (V (unV x + unV y))) asgn (myGenerate n fn)
      rhs = toList $ runIdentity $
              myGenerateM n (\idx -> Identity (V (unV (asgn C.! idx) + unV (fn idx))))
  lhs === rhs

------------------------------------------------------------------------
-- Test tree

tests :: TT.TestTree
tests = TT.testGroup "Assignment RULES (semantics)"
  [ testPropertyNamed "fmapFC/id" "prop_fmapFC_id" prop_fmapFC_id
  , testPropertyNamed "fmapFC/fmapFC" "prop_fmapFC_fmapFC" prop_fmapFC_fmapFC
  , testPropertyNamed "traverseFC/fmapFC" "prop_traverseFC_fmapFC" prop_traverseFC_fmapFC
  , testPropertyNamed "traverseFC/imapFC" "prop_traverseFC_imapFC" prop_traverseFC_imapFC
  , testPropertyNamed "itraverseFC/fmapFC" "prop_itraverseFC_fmapFC" prop_itraverseFC_fmapFC
  , testPropertyNamed "itraverseFC/imapFC" "prop_itraverseFC_imapFC" prop_itraverseFC_imapFC
  , testPropertyNamed "imapFC/fmapFC" "prop_imapFC_fmapFC" prop_imapFC_fmapFC
  , testPropertyNamed "imapFC/imapFC" "prop_imapFC_imapFC" prop_imapFC_imapFC
  , testPropertyNamed "fmapFC/imapFC" "prop_fmapFC_imapFC" prop_fmapFC_imapFC
  , testPropertyNamed "fmapFC/generate" "prop_fmapFC_generate" prop_fmapFC_generate
  , testPropertyNamed "imapFC/generate" "prop_imapFC_generate" prop_imapFC_generate
  , testPropertyNamed "(!)/fmapFC" "prop_index_fmapFC" prop_index_fmapFC
  , testPropertyNamed "(!)/imapFC" "prop_index_imapFC" prop_index_imapFC
  , testPropertyNamed "(!)/generate" "prop_index_generate" prop_index_generate
  , testPropertyNamed "traverseFC/generate" "prop_traverseFC_generate" prop_traverseFC_generate
  , testPropertyNamed "traverseWithIndex/generate" "prop_traverseWithIndex_generate" prop_traverseWithIndex_generate
  , testPropertyNamed "zipWithM/fmapFC_l" "prop_zipWithM_fmapFC_l" prop_zipWithM_fmapFC_l
  , testPropertyNamed "zipWithM/fmapFC_r" "prop_zipWithM_fmapFC_r" prop_zipWithM_fmapFC_r
  , testPropertyNamed "fmapFC/traverseFC" "prop_fmapFC_traverseFC" prop_fmapFC_traverseFC
  , testPropertyNamed "zipWithM/generate_l" "prop_zipWithM_generate_l" prop_zipWithM_generate_l
  , testPropertyNamed "zipWithM/generate_r" "prop_zipWithM_generate_r" prop_zipWithM_generate_r
  ]
