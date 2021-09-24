{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
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
import           Test.Tasty.HUnit (assertBool, testCase)

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Fin
import           Data.Parameterized.Some (Some(Some))

#if __GLASGOW_HASKELL__ >= 806
import qualified Hedgehog.Classes as HC
#endif

genFin :: (0 <= n, Monad m) => NatRepr n -> GenT m (Fin n)
genFin n =
  do x0 <- HG.integral (linear 0 ((natValue n) - 1 :: Natural))
     Some x <- return (mkNatRepr x0)
     return $
       case testLeq (incNat x) n of
         Just LeqProof -> mkFin x
         Nothing -> error "Impossible"

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
