{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module Test.Context
( contextTests
) where

import Test.Tasty
import Test.QuickCheck
import Test.Tasty.QuickCheck

import Control.Lens
import Data.Parameterized.Classes
import Data.Parameterized.TraversableFC
import Data.Parameterized.Some

import qualified Data.Parameterized.Context.Safe as S
import qualified Data.Parameterized.Context.Unsafe as U

data Payload (ty :: *) where
  IntPayload    :: Int -> Payload Int
  StringPayload :: String -> Payload String
  BoolPayload   :: Bool -> Payload Bool

instance TestEquality Payload where
  testEquality (IntPayload x) (IntPayload y) = if x == y then Just Refl else Nothing
  testEquality (StringPayload x) (StringPayload y) = if x == y then Just Refl else Nothing
  testEquality (BoolPayload x) (BoolPayload y) = if x == y then Just Refl else Nothing
  testEquality _ _ = Nothing

instance Show (Payload tp) where
  show (IntPayload x) = show x
  show (StringPayload x) = show x
  show (BoolPayload x) = show x

instance ShowF Payload

instance Arbitrary (Some Payload) where
  arbitrary = oneof
    [ Some . IntPayload <$> arbitrary
    , Some . StringPayload <$> arbitrary
    , Some . BoolPayload <$> arbitrary
    ]

type UAsgn = U.Assignment Payload
type SAsgn = S.Assignment Payload

mkUAsgn :: [Some Payload] -> Some UAsgn
mkUAsgn = go U.empty
 where go :: UAsgn ctx -> [Some Payload] -> Some UAsgn
       go a [] = Some a
       go a (Some x : xs) = go (U.extend a x) xs

mkSAsgn :: [Some Payload] -> Some SAsgn
mkSAsgn = go S.empty
 where go :: SAsgn ctx -> [Some Payload] -> Some SAsgn
       go a [] = Some a
       go a (Some x : xs) = go (S.extend a x) xs

instance Arbitrary (Some UAsgn) where
  arbitrary = mkUAsgn <$> arbitrary
instance Arbitrary (Some SAsgn) where
  arbitrary = mkSAsgn <$> arbitrary

twiddle :: Payload a -> Payload a
twiddle (IntPayload n) = IntPayload (n+1)
twiddle (StringPayload str) = StringPayload (str++"asdf")
twiddle (BoolPayload b) = BoolPayload (not b)

contextTests :: IO TestTree
contextTests = testGroup "Context" <$> return
   [ testProperty "safe_index_eq" $ \v vs i -> ioProperty $ do
         let vals = v:vs
         let i' = min (max 0 i) (length vals - 1)
         Some a <- return $ mkSAsgn vals
         Just (Some idx) <- return $ S.intIndex i' (S.size a)
         return (Some (a S.! idx) == vals !! i')
   , testProperty "unsafe_index_eq" $ \v vs i -> ioProperty $ do
         let vals = v:vs
         let i' = min (max 0 i) (length vals - 1)
         Some a <- return $ mkUAsgn vals
         Just (Some idx) <- return $ U.intIndex i' (U.size a)
         return (Some (a U.! idx) == vals !! i')
   , testProperty "safe_tolist" $ \vals -> ioProperty $ do
         Some a <- return $ mkSAsgn vals
         let vals' = toListFC Some a
         return (vals == vals')
   , testProperty "unsafe_tolist" $ \vals -> ioProperty $ do
         Some a <- return $ mkUAsgn vals
         let vals' = toListFC Some a
         return (vals == vals')
   , testProperty "adjust test monadic" $ \v vs i -> ioProperty $ do
         let vals = v:vs  -- ensures vals is not an empty array
         Some x <- return $ mkUAsgn vals
         Some y <- return $ mkSAsgn vals
         let i' = min (max 0 i) (length vals - 1)

         Just (Some idx_x) <- return $ U.intIndex i' (U.size x)
         Just (Some idx_y) <- return $ S.intIndex i' (S.size y)

         x' <- U.adjustM (return . twiddle) idx_x x
         y' <- S.adjustM (return . twiddle) idx_y y

         return (toListFC Some x' == toListFC Some y')

   , testProperty "adjust test" $ \v vs i -> ioProperty $ do
         let vals = v:vs  -- ensures vals is not an empty array
         Some x <- return $ mkUAsgn vals
         Some y <- return $ mkSAsgn vals
         let i' = min (max 0 i) (length vals - 1)

         Just (Some idx_x) <- return $ U.intIndex i' (U.size x)
         Just (Some idx_y) <- return $ S.intIndex i' (S.size y)

         let x' = over (ixF idx_x) twiddle x
             y' = (ixF idx_y) %~ twiddle $ y
             x'' = U.adjust twiddle idx_x x
             y'' = S.adjust twiddle idx_y y

         return (toListFC Some x' == toListFC Some y' &&
                 -- adjust actually modified the entry
                 toListFC Some x /= toListFC Some x' &&
                 toListFC Some y /= toListFC Some y' &&
                 -- verify new version is equivalent to older deprecated version
                 toListFC Some x'' == toListFC Some x' &&
                 toListFC Some y'' == toListFC Some y')

   , testProperty "update test" $ \v vs i -> ioProperty $ do
         let vals = v:vs  -- ensures vals is not an empty array
         Some x <- return $ mkUAsgn vals
         Some y <- return $ mkSAsgn vals
         let i' = min (max 0 i) (length vals - 1)

         Just (Some idx_x) <- return $ U.intIndex i' (U.size x)
         Just (Some idx_y) <- return $ S.intIndex i' (S.size y)

         let x' = over (ixF idx_x) twiddle x
             y' = (ixF idx_y) %~ twiddle $ y
             updX = set (ixF idx_x) (x' U.! idx_x) x
             updY = (ixF idx_y) .~  (y' S.! idx_y) $ y
             updX' = U.update idx_x (x' U.! idx_x) x
             updY' = S.update idx_y (y' S.! idx_y) y

         return (toListFC Some updX == toListFC Some updY &&
                 -- update actually modified the entry
                 toListFC Some x /= toListFC Some updX &&
                 toListFC Some y /= toListFC Some updY &&
                 -- update modified the expected entry
                 toListFC Some x' == toListFC Some updX &&
                 toListFC Some y' == toListFC Some updY &&
                 -- verify new version is equivalent to older deprecated version
                 toListFC Some updX == toListFC Some updX' &&
                 toListFC Some updY == toListFC Some updY'
                )

   , testProperty "safe_eq" $ \vals1 vals2 -> ioProperty $ do
         Some x <- return $ mkSAsgn vals1
         Some y <- return $ mkSAsgn vals2
         case testEquality x y of
           Just Refl -> return $ vals1 == vals2
           Nothing   -> return $ vals1 /= vals2
   , testProperty "unsafe_eq" $ \vals1 vals2 -> ioProperty $ do
         Some x <- return $ mkUAsgn vals1
         Some y <- return $ mkUAsgn vals2
         case testEquality x y of
           Just Refl -> return $ vals1 == vals2
           Nothing   -> return $ vals1 /= vals2
   ]
