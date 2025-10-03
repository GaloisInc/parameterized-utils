{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Test.Some
  ( someTests
  )
where

import           Data.Type.Equality (TestEquality(testEquality), (:~:)(Refl))
import           Lens.Micro (Lens', lens, set)
import           Lens.Micro.Extras (view)

import           Test.Tasty (TestTree, testGroup)
import           Test.Tasty.HUnit (assertEqual, testCase)

import           Data.Parameterized.Classes (ShowF)
import           Data.Parameterized.Some (Some(Some), someLens)

data Item b where
  BoolItem :: Item Bool
  IntItem :: Item Int

instance Show (Item b) where
  show =
    \case
      BoolItem -> "BoolItem"
      IntItem -> "IntItem"

instance TestEquality Item where
  testEquality x y =
    case (x, y) of
      (BoolItem, BoolItem) -> Just Refl
      (IntItem, IntItem) -> Just Refl
      _ -> Nothing

data Pair a b =
  Pair
    { _fir :: a
    , _sec :: Item b
    }

-- This instance isn't compatible with the intended use of TestEquality (which
-- is supposed to be just for singletons), but it seems fine for tests.
instance Eq a => TestEquality (Pair a) where
  testEquality x y =
    case testEquality (_sec x) (_sec y) of
      Just Refl -> if _fir x == _fir y then Just Refl else Nothing
      Nothing -> Nothing

instance (Show a) => Show (Pair a b) where
  show (Pair a b) = "Pair(" ++ show a ++ ", " ++ show b ++ ")"

instance Show a => ShowF (Pair a)

fir :: Lens' (Pair a b) a
fir = lens _fir (\s v -> s { _fir = v })

someFir :: Lens' (Some (Pair a)) a
someFir = someLens fir

someTests :: IO TestTree
someTests =
  testGroup "Some" <$>
    return
      [ testCase "someLens: view . set" $
          assertEqual
            "view l . set l x == const x"
            (view someFir (set someFir 5 (Some (Pair 1 BoolItem))))
            (5 :: Int)
      , testCase "someLens: set . set" $
          assertEqual
            "set l y . set l x == set l y"
            (set someFir 4 (set someFir 5 (Some (Pair 1 IntItem))))
            (Some (Pair (4 :: Int) IntItem))
      ]
