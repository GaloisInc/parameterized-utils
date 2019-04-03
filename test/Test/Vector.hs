{-# Language DataKinds #-}
{-# Language ExplicitForAll #-}
{-# Language TypeOperators #-}
{-# Language TypeFamilies #-}
{-# Language FlexibleInstances #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language CPP #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
#if __GLASGOW_HASKELL__ >= 805
{-# Language NoStarIsType #-}
#endif
module Test.Vector
( vecTests
) where

import Test.Tasty
import Test.Tasty.QuickCheck ( Arbitrary(..), testProperty, vectorOf )

import Data.Parameterized.NatRepr
import Data.Parameterized.Vector
import GHC.TypeLits
import Prelude hiding (reverse)


instance KnownNat n => Arbitrary (NatRepr n) where
  arbitrary = return knownNat


instance forall a n. ( 1 <= n
                     , Arbitrary a
                     , KnownNat n) =>
         Arbitrary (Vector n a) where
  arbitrary = do
    n <- arbitrary
    l <- vectorOf (widthVal n) arbitrary
    case fromList n l of
      Just v -> return v
      Nothing -> error ("fromList failure for size " <> show n)


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
      \n w v -> (v :: Vector (5 * 5) Ordering) ==
                (join (n :: NatRepr 5) $ split n (w :: NatRepr 5) $ v)
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
