{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}
module Test.Context.Elective
  ( electiveTests
  ) where

import Data.Functor.Compose (Compose(..))
import Test.Tasty (testGroup, TestTree)
import Test.Tasty.HUnit (testCase, (@?=))

import Data.Parameterized.Classes (KnownRepr(..))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Context.Elective as Ctx
import Data.Parameterized.TH.GADT (mkKnownReprs, mkRepr)

data Type = BoolType
          | IntType

$(mkRepr ''Type)
$(mkKnownReprs ''Type)

deriving instance Eq   (TypeRepr tp)
deriving instance Show (TypeRepr tp)

data Val (tp :: Type) where
  BoolVal :: Bool -> Val BoolType
  IntVal :: Int -> Val IntType

deriving instance Eq   (Val tp)
deriving instance Show (Val tp)

type Electives = Ctx.EmptyCtx Ctx.::> BoolType Ctx.::> IntType Ctx.::> BoolType

showWithIndex :: Ctx.Index ctx tp -> TypeRepr tp -> String
showWithIndex idx tpr = shows tpr . showChar '/' . shows idx $ ""

te0, te1, te2 :: Ctx.Elective TypeRepr Electives
te0 = Ctx.Elective Ctx.i1of3 knownRepr
te1 = Ctx.Elective Ctx.i2of3 knownRepr
te2 = Ctx.Elective Ctx.i3of3 knownRepr

ve0, ve0', ve1, ve1', ve2 :: Ctx.Elective Val Electives
ve0  = Ctx.Elective Ctx.i1of3 (BoolVal True)
ve0' = Ctx.Elective Ctx.i1of3 (BoolVal False)
ve1  = Ctx.Elective Ctx.i2of3 (IntVal 1)
ve1' = Ctx.Elective Ctx.i2of3 (IntVal 2)
ve2  = Ctx.Elective Ctx.i3of3 (BoolVal False)

electiveTests :: TestTree
electiveTests = testGroup "Elective"
  [ testCase "elective" $ do
      Ctx.elective show te0 @?= "BoolTypeRepr"
      Ctx.elective show te1 @?= "IntTypeRepr"
      Ctx.elective show te2 @?= "BoolTypeRepr"
  , testCase "ielective" $ do
      Ctx.ielective showWithIndex te0 @?= "BoolTypeRepr/0"
      Ctx.ielective showWithIndex te1 @?= "IntTypeRepr/1"
      Ctx.ielective showWithIndex te2 @?= "BoolTypeRepr/2"
  , testCase "elect" $ do
      let electives = [te0, te1, te2, te1, te0]
      Ctx.elect Ctx.i1of3 electives @?= [BoolTypeRepr, BoolTypeRepr]
      Ctx.elect Ctx.i2of3 electives @?= [IntTypeRepr, IntTypeRepr]
      Ctx.elect Ctx.i3of3 electives @?= [BoolTypeRepr]

      let valElectives = [ve0', ve1, ve0, ve2, ve1']
      Ctx.elect Ctx.i1of3 valElectives @?= [BoolVal False, BoolVal True]
      Ctx.elect Ctx.i2of3 valElectives @?= [IntVal 1, IntVal 2]
      Ctx.elect Ctx.i3of3 valElectives @?= [BoolVal False]
  , testCase "isElective" $ do
      Ctx.isElective Ctx.i1of3 te0 @?= True
      Ctx.isElective Ctx.i1of3 te1 @?= False
      Ctx.isElective Ctx.i1of3 te2 @?= False
      Ctx.isElective Ctx.i2of3 te0 @?= False
      Ctx.isElective Ctx.i2of3 te1 @?= True
      Ctx.isElective Ctx.i2of3 te2 @?= False
      Ctx.isElective Ctx.i3of3 te0 @?= False
      Ctx.isElective Ctx.i3of3 te1 @?= False
      Ctx.isElective Ctx.i3of3 te2 @?= True
  , testCase "fromElective" $ do
      Ctx.fromElective Ctx.i1of3 knownRepr te0 @?= knownRepr
      Ctx.fromElective Ctx.i1of3 knownRepr te1 @?= knownRepr
      Ctx.fromElective Ctx.i1of3 knownRepr te2 @?= knownRepr
      Ctx.fromElective Ctx.i2of3 knownRepr te0 @?= knownRepr
      Ctx.fromElective Ctx.i2of3 knownRepr te1 @?= knownRepr
      Ctx.fromElective Ctx.i2of3 knownRepr te2 @?= knownRepr
      Ctx.fromElective Ctx.i1of3 knownRepr te0 @?= knownRepr
      Ctx.fromElective Ctx.i1of3 knownRepr te1 @?= knownRepr
      Ctx.fromElective Ctx.i1of3 knownRepr te2 @?= knownRepr
  , testCase "partitionElectives" $ do
      let pes = Ctx.partitionElectives [te0, te1, te2, te1, te0]
      getCompose (pes Ctx.! Ctx.i1of3) @?= [BoolTypeRepr, BoolTypeRepr]
      getCompose (pes Ctx.! Ctx.i2of3) @?= [IntTypeRepr, IntTypeRepr]
      getCompose (pes Ctx.! Ctx.i3of3) @?= [BoolTypeRepr]

      let pes' = Ctx.partitionElectives [ve0', ve1, ve0, ve2, ve1']
      getCompose (pes' Ctx.! Ctx.i1of3) @?= [BoolVal False, BoolVal True]
      getCompose (pes' Ctx.! Ctx.i2of3) @?= [IntVal 1, IntVal 2]
      getCompose (pes' Ctx.! Ctx.i3of3) @?= [BoolVal False]
  ]
