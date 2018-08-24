{-# Language DataKinds #-}
{-# Language ExplicitForAll #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}

module Test.Vector
( vecTests
) where

import Test.Tasty
import Test.Tasty.QuickCheck (Arbitrary(..), Gen, testProperty)

import Data.Parameterized.NatRepr
import Data.Parameterized.Vector
import GHC.TypeLits
import Prelude hiding (reverse)

instance KnownNat n => Arbitrary (NatRepr n) where
  arbitrary = return knownNat

-- GHC thinks that this instances overlaps with the
-- "Arbitrary a => Arbitrary (Maybe a)" instance from QuickCheck, but it doesn't:
-- there is no "Arbitrary a => Arbitrary (Vector n a)".
instance {-# OVERLAPS #-} forall a n. (1 <= n, Arbitrary a, KnownNat n)
    => Arbitrary (Maybe (Vector n a)) where
  arbitrary = do
    n <- (arbitrary :: Gen (NatRepr n))
    l <- (arbitrary :: Gen [a])
    return $ fromList n l

-- We use @Ordering@ just because it's simple
vecTests :: IO TestTree
vecTests = testGroup "Vector" <$> return
  [ testProperty "reverse100" $
      \n v -> fromList (n :: NatRepr 100) (v :: [Ordering]) ==
              (reverse <$> (reverse <$> (fromList n v)))
  , testProperty "reverseSingleton" $
      \n v -> fromList (n :: NatRepr 1) (v :: [Ordering]) ==
              (reverse <$> (fromList n v))
  , testProperty "split-join" $
      \n w v -> (v :: Maybe (Vector (5 * 5) Ordering)) ==
                (join (n :: NatRepr 5) . split n (w :: NatRepr 5) <$> v)
  ]
