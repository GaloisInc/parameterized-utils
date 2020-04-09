module Test.NatRepr
  ( natTests
  )
where

import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           GHC.TypeLits

natTests :: IO TestTree
natTests = testGroup "Nat" <$> return
  [ testProperty "withKnownNat" $ property $ do
      nInt <- forAll $ HG.int (linearBounded :: Range Int)
      case someNat nInt of
        Nothing       -> diff nInt (<) 0
        Just (Some r) -> nInt === withKnownNat r (fromEnum $ natVal r)
  ]
