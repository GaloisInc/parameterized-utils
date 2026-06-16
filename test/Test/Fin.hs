{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# Language CPP #-}

module Test.Fin
  ( finTests
  , genFin
  )
where

import           Data.Hashable (hashWithSalt)
import           Numeric.Natural (Natural)

import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range (linear, linearBounded)
import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.Hedgehog (testPropertyNamed)
import           Test.Tasty.HUnit (assertBool, testCase)

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Fin
import           Data.Parameterized.Some (Some(Some))

#if __GLASGOW_HASKELL__ >= 806
import qualified Hedgehog.Classes as HC
#endif

genNatRepr :: (Monad m) => Natural -> GenT m (Some NatRepr)
genNatRepr bound =
  do x0 <- HG.integral (linear 0 bound)
     return (mkNatRepr x0)

genFin :: (1 <= n, Monad m) => NatRepr n -> GenT m (Fin n)
genFin n =
  do Some x <- genNatRepr (natValue n - 1 :: Natural)
     return $
       case testLeq (incNat x) n of
         Just LeqProof -> mkFin x
         Nothing -> error "Impossible"

prop_eq_hash :: Property
prop_eq_hash = property $
  do salt <- forAll (HG.int linearBounded)
     (f1, f2) <- forAll $
                 HG.filter (\(f1, f2) -> f1 == f2) $
                 (,) <$> genFin (knownNat @100) <*> genFin (knownNat @100)
     hashWithSalt salt f1 === hashWithSalt salt f2

prop_count_true :: Property
prop_count_true = property $
  do Some n <- forAll (genNatRepr 100)
     finToNat (countFin n (\_ _ -> True)) === natValue n

prop_count_false :: Property
prop_count_false = property $
  do Some n <- forAll (genNatRepr 100)
     finToNat (countFin n (\_ _ -> False)) === 0

prop_add_comm :: Property
prop_add_comm = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     b <- forAll (genFin n10)
     (a + b) === (b + a)

prop_add_identity :: Property
prop_add_identity = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     (mkFin (knownNat @0) + a) === a

prop_add_inverse :: Property
prop_add_inverse = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     (a + negate a) === mkFin (knownNat @0)

prop_add_assoc :: Property
prop_add_assoc = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     b <- forAll (genFin n10)
     c <- forAll (genFin n10)
     a + (b + c) === (a + b) + c

prop_add_negate_sub :: Property
prop_add_negate_sub = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     b <- forAll (genFin n10)
     (a + negate b) === (a - b)

prop_sub_anticomm :: Property
prop_sub_anticomm = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     b <- forAll (genFin n10)
     (a - b) === negate (b - a)

prop_mul_comm :: Property
prop_mul_comm = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     b <- forAll (genFin n10)
     (a * b) === (b * a)

prop_mul_identity :: Property
prop_mul_identity = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     (mkFin (knownNat @1) * a) === a

prop_mul_assoc :: Property
prop_mul_assoc = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     b <- forAll (genFin n10)
     c <- forAll (genFin n10)
     a * (b * c) === (a * b) * c

prop_mul_annihilate :: Property
prop_mul_annihilate = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     (mkFin (knownNat @0) * a) === mkFin (knownNat @0)

prop_neg_inv :: Property
prop_neg_inv = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     negate (negate a) === a

prop_abs_idem :: Property
prop_abs_idem = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     abs (abs a) === abs a

prop_signum_idem :: Property
prop_signum_idem = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     signum (signum a) === signum a

prop_abs_signum :: Property
prop_abs_signum = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     (abs a * signum a) === a

prop_recip_1 :: Property
prop_recip_1 = property $
  do let n1 = knownNat @1
     a <- forAll (genFin n1)
     recipFinModN n1 a === Just (mkFin (knownNat @0))

prop_recip_10 :: Property
prop_recip_10 = property $
  do let n10 = knownNat @10
     a <- forAll (genFin n10)
     let aInv = recipFinModN n10 a
     let d = gcd (finToNat a) (natValue n10)
     case aInv of
       Nothing ->
         assert $ d >= 1
       Just aInv' ->
         do d === 1
            (a * aInv') === mkFin (knownNat @1)

finTests :: IO TestTree
finTests =
  testGroup "Fin" <$>
    return
      [ testCase "minBound <= maxBound (1)" $
          assertBool
            "minBound <= maxBound (1)"
            ((minBound :: Fin 1) <= (minBound :: Fin 1))
      , testCase "minBound <= maxBound (2)" $
          assertBool
            "minBound <= maxBound (2)"
            ((minBound :: Fin 2) <= (minBound :: Fin 2))
      , testCase "show (minFin @1) == \"Fin 0\"" $
          assertBool
            "show (minFin @1) == \"Fin 0\""
            (show (minFin @1) == "Fin 0")
      , testCase "show (Just (minFin @1)) == \"Just (Fin 0)\"" $
          assertBool
            "show (Just (minFin @1)) == \"Just (Fin 0)\""
            (show (Just (minFin @1)) == "Just (Fin 0)")

      , testPropertyNamed
          "Eq equality implies hash equality"
          "prop_eq_hash"
          prop_eq_hash

      , testPropertyNamed "count-true" "prop_count_true" prop_count_true
      , testPropertyNamed "count-false" "prop_count_false" prop_count_false

      , testPropertyNamed "add-comm" "prop_add_comm" prop_add_comm
      , testPropertyNamed "add-identity" "prop_add_identity" prop_add_identity
      , testPropertyNamed "add-inverse" "prop_add_inverse" prop_add_inverse
      , testPropertyNamed "add-assoc" "prop_add_assoc" prop_add_assoc
      , testPropertyNamed "add-negate-sub" "prop_add_negate_sub" prop_add_negate_sub
      , testPropertyNamed "sub-anticomm" "prop_sub_anticomm" prop_sub_anticomm
      , testPropertyNamed "mul-comm" "prop_mul_comm" prop_mul_comm
      , testPropertyNamed "mul-identity" "prop_mul_identity" prop_mul_identity
      , testPropertyNamed "mul-annihilate" "prop_mul_annihilate" prop_mul_annihilate
      , testPropertyNamed "mul-assoc" "prop_mul_assoc" prop_mul_assoc
      , testPropertyNamed "neg-inv" "prop_neg_inv" prop_neg_inv
      , testPropertyNamed "abs-idem" "prop_abs_idem" prop_abs_idem
      , testPropertyNamed "signum-idem" "prop_signum_idem" prop_signum_idem
      , testPropertyNamed "abs-signum" "prop_abs_signum" prop_abs_signum

      , testPropertyNamed "recip-1" "prop_recip_1" prop_recip_1
      , testPropertyNamed "recip-10" "prop_recip_10" prop_recip_10

#if __GLASGOW_HASKELL__ >= 806
      , testCase "Eq-Fin-laws-1" $
          assertBool "Eq-Fin-laws-1" =<<
            HC.lawsCheck (HC.eqLaws (genFin (knownNat @1)))

      , testCase "Ord-Fin-laws-1" $
          assertBool "Ord-Fin-laws-1" =<<
            HC.lawsCheck (HC.ordLaws (genFin (knownNat @1)))

      , testCase "Eq-Fin-laws-10" $
          assertBool "Eq-Fin-laws-10" =<<
            HC.lawsCheck (HC.eqLaws (genFin (knownNat @10)))

      , testCase "Ord-Fin-laws-10" $
          assertBool "Ord-Fin-laws-10" =<<
            HC.lawsCheck (HC.ordLaws (genFin (knownNat @10)))
#endif
      ]
