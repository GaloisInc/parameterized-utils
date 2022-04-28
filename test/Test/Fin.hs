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

import           Numeric.Natural (Natural)

import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range (linear)
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

prop_count_true :: Property
prop_count_true = property $
  do Some n <- forAll (genNatRepr 100)
     finToNat (countFin n (\_ _ -> True)) === natValue n

prop_count_false :: Property
prop_count_false = property $
  do Some n <- forAll (genNatRepr 100)
     finToNat (countFin n (\_ _ -> False)) === 0

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

      , testPropertyNamed "count-true" "prop_count_true" prop_count_true
      , testPropertyNamed "count-false" "prop_count_false" prop_count_false

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
