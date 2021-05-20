{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Test.TH
  ( thTests
  )
where

import           Test.Tasty
import           Test.Tasty.HUnit

import           Control.Monad (when)
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.TH.GADT
import           GHC.TypeNats

data T1 = A | B | C
$(mkRepr ''T1)
$(mkKnownReprs ''T1)
$(return [])
instance TestEquality T1Repr where
  testEquality = $(structuralTypeEquality [t|T1Repr|] [])
deriving instance Show (T1Repr t)

data T2 = T2_1 T1 | T2_2 Nat
$(mkRepr ''T2)
$(mkKnownReprs ''T2)
$(return [])
instance TestEquality T2Repr where
  testEquality = $(structuralTypeEquality [t|T2Repr|]
                    [ (AnyType, [|testEquality|]) ])
deriving instance Show (T2Repr t)

eqTest :: (TestEquality f, Show (f a), Show (f b)) => f a -> f b -> IO ()
eqTest a b =
  when (not (isJust (testEquality a b))) $ assertFailure $ show a ++ " /= " ++ show b

neqTest :: (TestEquality f, Show (f a), Show (f b)) => f a -> f b -> IO ()
neqTest a b =
  when (isJust (testEquality a b)) $ assertFailure $ show a ++ " == " ++ show b

thTests :: IO TestTree
thTests = testGroup "TH" <$> return
  [ testCase "Repr equality test" $ do
      -- T1
      ARepr `eqTest` ARepr
      ARepr `neqTest` BRepr
      BRepr `eqTest` BRepr
      BRepr `neqTest` CRepr
      -- T2
      T2_1Repr ARepr `eqTest` T2_1Repr ARepr
      T2_2Repr (knownNat @5) `eqTest` T2_2Repr (knownNat @5)
      T2_1Repr ARepr `neqTest` T2_1Repr CRepr
      T2_2Repr (knownNat @5) `neqTest` T2_2Repr (knownNat @9)
      T2_1Repr BRepr `neqTest` T2_2Repr (knownNat @4)

  , testCase "KnownRepr test" $ do
      -- T1
      let aRepr = knownRepr :: T1Repr 'A
          bRepr = knownRepr :: T1Repr 'B
          cRepr = knownRepr :: T1Repr 'C
      aRepr `eqTest` ARepr
      bRepr `eqTest` BRepr
      cRepr `eqTest` CRepr
      --T2
      let t2ARepr = knownRepr :: T2Repr ('T2_1 'A)
          t2BRepr = knownRepr :: T2Repr ('T2_1 'B)
          t25Repr = knownRepr :: T2Repr ('T2_2 5)
      t2ARepr `eqTest` T2_1Repr ARepr
      t2BRepr `eqTest` T2_1Repr BRepr
      t25Repr `eqTest` T2_2Repr (knownNat @5)
      t2ARepr `neqTest` t2BRepr
      t2ARepr `neqTest` t25Repr
      t2BRepr `neqTest` t25Repr
  ]
