module Test.NatRepr
( natTests
) where

import Test.Tasty
import Test.Tasty.QuickCheck

import Data.Parameterized.NatRepr
import Data.Parameterized.Some
import GHC.TypeLits

natTests :: IO TestTree
natTests = testGroup "Nat" <$> return
  [ testProperty "withKnownNat" $ \nInt ->
      case someNat nInt of
        Nothing -> nInt < 0
        Just (Some r) -> nInt == withKnownNat r (natVal r)
  ]
