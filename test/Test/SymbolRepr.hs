{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Test.SymbolRepr
  (
    symbolTests
  )
where

import           Test.Tasty
import           Test.Tasty.HUnit ( (@=?), testCase )

import           Data.Parameterized.SymbolRepr
import           GHC.TypeLits


data Bird (name :: Symbol) where
  Jay :: String -> Bird "Jay"
  Dove :: Bird "Dove"
  Hawk :: Bird "Hawk"

symbolTests :: IO TestTree
symbolTests = testGroup "Symbol" <$> return
  [
    testCase "SomeSym" $ do
      "Jay"  @=? viewSomeSym symbolVal (SomeSym (Jay "Blue"))
      "Dove" @=? viewSomeSym symbolVal (SomeSym Dove)
      "Hawk" @=? viewSomeSym symbolVal (SomeSym Hawk)

  ]
