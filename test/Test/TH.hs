{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

module Test.TH
  ( thTests
  )
where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad (when)
import Data.Parameterized.Classes
import Data.Parameterized.NatRepr
import Data.Parameterized.SymbolRepr
import Data.Parameterized.TH.GADT
import GHC.TypeNats

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

data T3 (is_a :: Symbol) where
  T3_Int :: Int -> T3 "int"
  T3_Bool :: Bool -> T3 "bool"
$(return [])
instance TestEquality T3 where
  testEquality = $(structuralTypeEquality [t|T3|] [])
instance Eq (T3 s) where
  (==) = $(structuralEquality [t|T3|] [])
deriving instance Show (T3 s)

data T4 b (is_a :: Symbol) where
  T4_Int :: Int -> T4 b "int"
  T4_Bool :: Bool -> T4 b "bool"
$(return [])
instance TestEquality (T4 b) where
  testEquality = $(structuralTypeEquality [t|T4|] [])
instance Eq (T4 b s) where
  (==) = $(structuralEquality [t|T4|] [])
deriving instance Show (T4 b s)

eqTest :: (TestEquality f, Show (f a), Show (f b)) => f a -> f b -> IO ()
eqTest a b =
  when (not (isJust (testEquality a b))) $ assertFailure $ show a ++ " /= " ++ show b

neqTest :: (TestEquality f, Show (f a), Show (f b)) => f a -> f b -> IO ()
neqTest a b =
  when (isJust (testEquality a b))
  $ assertFailure
  $ show a <> " == " <> show b <> " but should not be!"

assertNotEqual :: (Eq a, Show a) => String -> a -> a -> IO ()
assertNotEqual msg a b =
  when (a == b)
  $ assertFailure
  $ msg <> " " <> show a <> " == " <> show b <> " but should not be!"

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

  , testCase "Instance tests" $ do
      assertEqual "T3_Int values" (T3_Int 5) (T3_Int 5)
      assertNotEqual "T3_Int values" (T3_Int 5) (T3_Int 54)
      assertEqual "T3_Bool values" (T3_Bool True) (T3_Bool True)
      assertNotEqual "T3_Bool values" (T3_Bool True) (T3_Bool False)

      -- n.b. the following is not possible: 'T3 "int"' is not a 'T3 "bool"'
      -- assertEqual "T3_Int/T3_Bool values" (T3_Int 1) (T3_Bool True)

      T3_Int 1 `eqTest` T3_Int 1
      T3_Int 1 `neqTest` T3_Int 3
      T3_Int 1 `neqTest` T3_Bool True
      T3_Bool False `neqTest` T3_Bool True
      T3_Bool True `eqTest` T3_Bool True

      assertEqual "T4_Int values" (T4_Int @String 5) (T4_Int @String 5)
      assertNotEqual "T4_Int values" (T4_Int @String 5) (T4_Int @String 54)

      T4_Int @String 1 `eqTest` T4_Int @String 1
      T4_Int @String 1 `neqTest` T4_Int @String 2


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
