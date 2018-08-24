{-# Language DataKinds #-}
{-# Language FlexibleInstances #-}
{-# Language StandaloneDeriving #-}

module Test.Vector
( vecTests
) where

import Test.Tasty
import Test.Tasty.QuickCheck

import Data.Parameterized.NatRepr
import Data.Parameterized.Vector
import GHC.TypeLits
import Prelude hiding (reverse)

instance KnownNat n => Arbitrary (NatRepr n) where
  arbitrary = return knownNat

vecTests :: IO TestTree
vecTests = testGroup "Vector" <$> return
  [ testProperty "reverse100" $
      \n v -> fromList (n :: NatRepr 100) (v :: [Int]) ==
              (reverse <$> (reverse <$> (fromList n v)))
  , testProperty "reverseSingleton" $
      \n v -> fromList (n :: NatRepr 1) (v :: [Int]) ==
              (reverse <$> (fromList n v))
  ]
