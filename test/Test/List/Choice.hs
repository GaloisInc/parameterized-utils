{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
module Test.List.Choice
  ( tests
  ) where

import qualified Data.Parameterized.List as PL
import Test.Tasty ( testGroup, TestTree )
import Data.Parameterized.Classes ( KnownRepr(knownRepr) )
import Data.Parameterized.TH.GADT (mkRepr, mkKnownReprs)
import Test.Tasty.HUnit ( testCase, (@?=) )

data Type = BoolType
          | IntType

$(mkRepr ''Type)
$(mkKnownReprs ''Type)

deriving instance Eq (TypeRepr tp)
deriving instance Show (TypeRepr tp)

data Val tp where
  BoolVal :: Bool -> Val 'BoolType
  IntVal :: Int -> Val 'IntType

deriving instance Eq (Val tp)
deriving instance Show (Val tp)

type Choices = ['BoolType, 'IntType, 'BoolType]

choice0, choice1, choice2 :: PL.Choice TypeRepr Choices
choice0 = PL.Choice PL.index0 knownRepr
choice1 = PL.Choice PL.index1 knownRepr
choice2 = PL.Choice PL.index2 knownRepr

valChoice0, valChoice0', valChoice1, valChoice1', valChoice2 :: PL.Choice Val Choices
valChoice0  = PL.Choice PL.index0 (BoolVal True)
valChoice0' = PL.Choice PL.index0 (BoolVal False)
valChoice1  = PL.Choice PL.index1 (IntVal 1)
valChoice1' = PL.Choice PL.index1 (IntVal 2)
valChoice2  = PL.Choice PL.index2 (BoolVal False)

reprToString :: TypeRepr tp -> String
reprToString BoolTypeRepr = "Bool"
reprToString IntTypeRepr = "Int"

indexToInt :: PL.Index tps tp -> Int
indexToInt PL.IndexHere = 0
indexToInt (PL.IndexThere ix) = 1 + indexToInt ix

choiceToString :: PL.Index Choices tp -> TypeRepr tp -> String
choiceToString ix tp = reprToString tp ++ "/" ++ show (indexToInt ix)

tests :: TestTree
tests = testGroup "List.Choice"
  [ testCase "choice" $ do
      PL.choice reprToString choice0 @?= "Bool"
      PL.choice reprToString choice1 @?= "Int"
      PL.choice reprToString choice2 @?= "Bool"
  , testCase "ichoice" $ do
      PL.ichoice choiceToString choice0 @?= "Bool/0"
      PL.ichoice choiceToString choice1 @?= "Int/1"
      PL.ichoice choiceToString choice2 @?= "Bool/2"
  , testCase "choose" $ do
      let choices = [choice0, choice1, choice2, choice1, choice0]
      PL.choose PL.index0 choices @?= [BoolTypeRepr, BoolTypeRepr]
      PL.choose PL.index1 choices @?= [IntTypeRepr, IntTypeRepr]
      PL.choose PL.index2 choices @?= [BoolTypeRepr]

      let valChoices = [valChoice0', valChoice1, valChoice0, valChoice2, valChoice1']
      PL.choose PL.index0 valChoices @?= [BoolVal False, BoolVal True]
      PL.choose PL.index1 valChoices @?= [IntVal 1, IntVal 2]
      PL.choose PL.index2 valChoices @?= [BoolVal False]
  , testCase "isChoice" $ do
      PL.isChoice PL.index0 choice0 @?= True
      PL.isChoice PL.index0 choice1 @?= False
      PL.isChoice PL.index0 choice2 @?= False
      PL.isChoice PL.index1 choice0 @?= False
      PL.isChoice PL.index1 choice1 @?= True
      PL.isChoice PL.index1 choice2 @?= False
      PL.isChoice PL.index2 choice0 @?= False
      PL.isChoice PL.index2 choice1 @?= False
      PL.isChoice PL.index2 choice2 @?= True
  , testCase "fromChoice" $ do
      PL.fromChoice PL.index0 knownRepr choice0 @?= knownRepr
      PL.fromChoice PL.index0 knownRepr choice1 @?= knownRepr
      PL.fromChoice PL.index0 knownRepr choice2 @?= knownRepr
      PL.fromChoice PL.index1 knownRepr choice0 @?= knownRepr
      PL.fromChoice PL.index1 knownRepr choice1 @?= knownRepr
      PL.fromChoice PL.index1 knownRepr choice2 @?= knownRepr
      PL.fromChoice PL.index0 knownRepr choice0 @?= knownRepr
      PL.fromChoice PL.index0 knownRepr choice1 @?= knownRepr
      PL.fromChoice PL.index0 knownRepr choice2 @?= knownRepr
  , testCase "partitionChoices" $ do
      let pcs = PL.partitionChoices [choice0, choice1, choice2, choice1, choice0]
      pcs PL.!! PL.index0 @?= PL.ChoiceList [BoolTypeRepr, BoolTypeRepr]
      pcs PL.!! PL.index1 @?= PL.ChoiceList [IntTypeRepr, IntTypeRepr]
      pcs PL.!! PL.index2 @?= PL.ChoiceList [BoolTypeRepr]

      let pcs' = PL.partitionChoices [valChoice0', valChoice1, valChoice0, valChoice2, valChoice1']
      pcs' PL.!! PL.index0 @?= PL.ChoiceList [BoolVal False, BoolVal True]
      pcs' PL.!! PL.index1 @?= PL.ChoiceList [IntVal 1, IntVal 2]
      pcs' PL.!! PL.index2 @?= PL.ChoiceList [BoolVal False]
  ]
