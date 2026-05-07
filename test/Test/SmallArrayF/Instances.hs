{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}

-- | Typeclass-laws tests for 'SmallArrayF' instances.
--
-- Uses @hedgehog-classes@ for the base laws, with a generator that
-- produces existentially-wrapped arrays of varying length and
-- contents; 'Some''s 'Eq' / 'Ord' / 'Show' / 'Hashable' instances
-- already delegate to the parameterized instances on 'SmallArrayF'.
-- The 'FunctorFC' / 'FoldableFC' / 'TraversableFC' laws are
-- hand-written Hedgehog properties, since @hedgehog-classes@ does not
-- cover those classes.
module Test.SmallArrayF.Instances (tests) where

import Control.DeepSeq (NFData(rnf))
import Data.Functor.Identity (Identity(Identity, runIdentity))
import Data.Hashable (hashWithSalt)
import Data.Kind (Type)
import qualified Data.Parameterized.Context as Ctx
import Data.Parameterized.Classes (HashableF(..), OrdF(..), OrderingF(..), ShowF, TestEquality(..), (:~:)(Refl))
import qualified Data.Parameterized.SmallArrayF as SAF
import Data.Parameterized.SmallArrayF (SmallArrayF)
import Data.Parameterized.Some
import Data.Parameterized.TraversableFC
import Data.Parameterized.TraversableFC.WithIndex
import Hedgehog
import qualified Hedgehog.Classes as HC
import qualified Hedgehog.Gen as HG
import Hedgehog.Range (linear)
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH
import Test.Tasty.Hedgehog (testPropertyNamed)

----------------------------------------------------------------------
-- Payload: a GADT indexed by 'Ordering' or 'Bool', so 'TestEquality'
-- and 'OrdF' can be written honestly (no unsafe coercions).

data P (tp :: Type) where
  PO :: Ordering -> P Ordering
  PB :: Bool -> P Bool

deriving instance Eq (P tp)
deriving instance Ord (P tp)
deriving instance Show (P tp)

instance ShowF P

instance TestEquality P where
  testEquality (PO x) (PO y) = if x == y then Just Refl else Nothing
  testEquality (PB x) (PB y) = if x == y then Just Refl else Nothing
  testEquality _ _ = Nothing

instance OrdF P where
  compareF (PO x) (PO y) = case compare x y of
    LT -> LTF
    EQ -> EQF
    GT -> GTF
  compareF (PB x) (PB y) = case compare x y of
    LT -> LTF
    EQ -> EQF
    GT -> GTF
  compareF PO{} PB{} = LTF
  compareF PB{} PO{} = GTF

instance HashableF P where
  hashWithSaltF s (PO o) = hashWithSalt s (0 :: Int, fromEnum o)
  hashWithSaltF s (PB b) = hashWithSalt s (1 :: Int, b)

----------------------------------------------------------------------
-- Generators

genP :: Gen (Some P)
genP = HG.choice
  [ Some . PO <$> HG.element [LT, EQ, GT]
  , Some . PB <$> HG.element [True, False]
  ]

genPList :: Gen [Some P]
genPList = HG.list (linear 0 8) genP

mkArr :: [Some P] -> Some (SmallArrayF P)
mkArr vals =
  case go Ctx.empty vals of
    Some a -> Some (SAF.fromAssignment a)
  where
    go :: Ctx.Assignment P ctx -> [Some P] -> Some (Ctx.Assignment P)
    go acc [] = Some acc
    go acc (Some x : xs) = go (Ctx.extend acc x) xs

genSomeSA :: Gen (Some (SmallArrayF P))
genSomeSA = mkArr <$> genPList

showOf :: P tp -> String
showOf (PO o) = "O " ++ show o
showOf (PB b) = "B " ++ show b

toListStr :: SmallArrayF P ctx -> [String]
toListStr = foldrFC (\x r -> showOf x : r) []

----------------------------------------------------------------------
-- FunctorFC laws

-- fmapFC id = id
prop_fmapFC_identity :: Property
prop_fmapFC_identity = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  toListStr (fmapFC id a) === toListStr a

-- fmapFC (f . g) = fmapFC f . fmapFC g
prop_fmapFC_composition :: Property
prop_fmapFC_composition = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  toListStr (fmapFC (shift . flipOrd) a) === toListStr (fmapFC shift (fmapFC flipOrd a))

-- Rotate 'LT → EQ → GT → LT'; identity elsewhere.
shift :: P tp -> P tp
shift (PO LT) = PO EQ
shift (PO EQ) = PO GT
shift (PO GT) = PO LT
shift (PB b)  = PB b

-- Flip 'LT <-> GT'; identity elsewhere.
flipOrd :: P tp -> P tp
flipOrd (PO LT) = PO GT
flipOrd (PO GT) = PO LT
flipOrd (PO EQ) = PO EQ
flipOrd (PB b)  = PB (not b)

----------------------------------------------------------------------
-- FoldableFC laws

-- foldMapFC f = foldrFC (mappend . f) mempty
prop_foldMapFC_foldrFC :: Property
prop_foldMapFC_foldrFC = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  let f x = [showOf x]
  foldMapFC f a === foldrFC (mappend . f) mempty a

----------------------------------------------------------------------
-- TraversableFC laws

-- traverseFC Identity = Identity
prop_traverseFC_identity :: Property
prop_traverseFC_identity = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  toListStr (runIdentity (traverseFC Identity a)) === toListStr a

-- traverseFC (Identity . f) = Identity . fmapFC f
prop_traverseFC_fmapFC :: Property
prop_traverseFC_fmapFC = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  toListStr (runIdentity (traverseFC (Identity . shift) a)) === toListStr (fmapFC shift a)

----------------------------------------------------------------------
-- FunctorFCWithIndex / FoldableFCWithIndex laws

-- imapFC (\_ x -> f x) = fmapFC f
prop_imapFC_const_fmapFC :: Property
prop_imapFC_const_fmapFC = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  toListStr (imapFC (\_ x -> shift x) a) === toListStr (fmapFC shift a)

-- ifoldMapFC (\_ x -> f x) = foldMapFC f
prop_ifoldMapFC_const_foldMapFC :: Property
prop_ifoldMapFC_const_foldMapFC = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  let f x = [showOf x]
  ifoldMapFC (\_ x -> f x) a === foldMapFC f a

----------------------------------------------------------------------
-- NFData: rnf terminates on random arrays.

prop_rnf_total :: Property
prop_rnf_total = property $ do
  vals <- forAll genPList
  Some a <- pure $ mkArr vals
  rnf a === ()

----------------------------------------------------------------------
-- Test tree

hcLawsCase :: String -> HC.Laws -> TT.TestTree
hcLawsCase name laws =
  TTH.testCase name $
    TTH.assertBool name =<< HC.lawsCheck laws

tests :: TT.TestTree
tests = TT.testGroup "SmallArrayF instances"
  [ TT.testGroup "hedgehog-classes"
    [ hcLawsCase "Eq" (HC.eqLaws genSomeSA)
    , hcLawsCase "Ord" (HC.ordLaws genSomeSA)
    , hcLawsCase "Show" (HC.showLaws genSomeSA)
    ]
  , TT.testGroup "FunctorFC"
    [ testPropertyNamed "identity" "prop_fmapFC_identity" prop_fmapFC_identity
    , testPropertyNamed "composition" "prop_fmapFC_composition" prop_fmapFC_composition
    ]
  , TT.testGroup "FoldableFC"
    [ testPropertyNamed "foldMapFC_via_foldrFC" "prop_foldMapFC_foldrFC" prop_foldMapFC_foldrFC
    ]
  , TT.testGroup "TraversableFC"
    [ testPropertyNamed "identity" "prop_traverseFC_identity" prop_traverseFC_identity
    , testPropertyNamed "fmapFC_agreement" "prop_traverseFC_fmapFC" prop_traverseFC_fmapFC
    ]
  , TT.testGroup "WithIndex"
    [ testPropertyNamed "imapFC_const_fmapFC" "prop_imapFC_const_fmapFC" prop_imapFC_const_fmapFC
    , testPropertyNamed "ifoldMapFC_const_foldMapFC" "prop_ifoldMapFC_const_foldMapFC" prop_ifoldMapFC_const_foldMapFC
    ]
  , TT.testGroup "NFData"
    [ testPropertyNamed "rnf_total" "prop_rnf_total" prop_rnf_total
    ]
  ]
