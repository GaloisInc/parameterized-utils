{-# Language DataKinds #-}
{-# Language ExplicitForAll #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language CPP #-}
#if __GLASGOW_HASKELL__ >= 805
{-# Language NoStarIsType #-}
#endif
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
--
-- While it might seem like this would just successfully generate a lot
-- of "Nothing", it does a pretty good job. Just try changing one of the tests!
instance {-# OVERLAPS #-} forall a n. (1 <= n, Arbitrary a, KnownNat n)
    => Arbitrary (Maybe (Vector n a)) where
  arbitrary = do
    n <- (arbitrary :: Gen (NatRepr n))
    l <- (arbitrary :: Gen [a])
    return $ fromList n l

instance Show (Int -> Ordering) where
  show _ = "unshowable"

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
  -- @cons@ is the same for vectors or lists
  , testProperty "cons" $
      \n v x -> (cons x <$> fromList (n :: NatRepr 20) (v :: [Ordering])) ==
                (fromList (incNat n) (x:v))
  -- @snoc@ is like appending to a list
  , testProperty "snoc" $
      \n v x -> (flip snoc x <$> fromList (n :: NatRepr 20) (v :: [Ordering])) ==
                (fromList (incNat n) (v ++ [x]))
  -- @generate@ is like mapping a function over indices
  , testProperty "generate" $
      \n f -> Just (generate (n :: NatRepr 55) ((f :: Int -> Ordering) . widthVal)) ==
              (fromList (incNat n) (map f [0..widthVal n]) :: Maybe (Vector 56 Ordering))
  ]
