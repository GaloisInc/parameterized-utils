{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
module Test.Context
  ( contextTests
  )
where

import           Control.Lens
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as C
import qualified Data.Parameterized.Ctx.Proofs as P
import qualified Data.Parameterized.Context.Safe as S
import qualified Data.Parameterized.Context.Unsafe as U
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range
import           Test.Tasty
import           Test.Tasty.Hedgehog

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

genSomePayload :: Monad m => GenT m (Some Payload)
genSomePayload = HG.choice [ Some . IntPayload    <$> HG.integral (linearBounded :: Range Int)
                           , Some . StringPayload <$> HG.string (linear 1 32) HG.ascii
                           , Some . BoolPayload   <$> HG.element [ True, False ]
                           ]

-- generate a non-empty list of payload entries
genSomePayloadList :: Monad m => GenT m [Some Payload]
genSomePayloadList = HG.list (linear 1 10) genSomePayload


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


twiddle :: Payload a -> Payload a
twiddle (IntPayload n) = IntPayload (n+1)
twiddle (StringPayload str) = StringPayload (str++"asdf")
twiddle (BoolPayload b) = BoolPayload (not b)


contextTests :: IO TestTree
contextTests = testGroup "Context" <$> return
   [ testProperty "safe_index_eq" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)
        Some a <- return $ mkSAsgn vals
        Just (Some idx) <- return $ S.intIndex i' (S.size a)
        Some (a S.! idx) === vals !! i'

   , testProperty "unsafe_index_eq" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)
        Some a <- return $ mkUAsgn vals
        Just (Some idx) <- return $ U.intIndex i' (U.size a)
        Some (a U.! idx) === vals !! i'

   , testProperty "safe_tolist" $ property $
     do vals <- forAll genSomePayloadList
        Some a <- return $ mkSAsgn vals
        let vals' = toListFC Some a
        vals === vals'
   , testProperty "unsafe_tolist" $ property $
     do vals <- forAll genSomePayloadList
        Some a <- return $ mkUAsgn vals
        let vals' = toListFC Some a
        vals === vals'

   , testProperty "adjust test monadic" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)

        Some x <- return $ mkUAsgn vals
        Some y <- return $ mkSAsgn vals

        Just (Some idx_x) <- return $ U.intIndex i' (U.size x)
        Just (Some idx_y) <- return $ S.intIndex i' (S.size y)

        x' <- U.adjustM (return . twiddle) idx_x x
        y' <- S.adjustM (return . twiddle) idx_y y

        toListFC Some x' === toListFC Some y'

   , testProperty "adjust test" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)

        Some x <- return $ mkUAsgn vals
        Some y <- return $ mkSAsgn vals

        Just (Some idx_x) <- return $ U.intIndex i' (U.size x)
        Just (Some idx_y) <- return $ S.intIndex i' (S.size y)

        let x' = x & ixF idx_x %~ twiddle
            y' = y & ixF idx_y %~ twiddle

        toListFC Some x' === toListFC Some y'
        -- adjust actually modified the entry
        toListFC Some x /== toListFC Some x'
        toListFC Some y /== toListFC Some y'

   , testProperty "update test" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)

        Some x <- return $ mkUAsgn vals
        Some y <- return $ mkSAsgn vals

        Just (Some idx_x) <- return $ U.intIndex i' (U.size x)
        Just (Some idx_y) <- return $ S.intIndex i' (S.size y)

        let x' = over (ixF idx_x) twiddle x
            y' = (ixF idx_y) %~ twiddle $ y
            updX = x & ixF idx_x .~ x' U.! idx_x
            updY = y & ixF idx_y .~ y' S.! idx_y

        toListFC Some updX === toListFC Some updY
        -- update actually modified the entry
        toListFC Some x /== toListFC Some updX
        toListFC Some y /== toListFC Some updY
        -- update modified the expected entry
        toListFC Some x' === toListFC Some updX
        toListFC Some y' === toListFC Some updY

   , testProperty "safe_eq" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkSAsgn vals1
        Some y <- return $ mkSAsgn vals2
        case testEquality x y of
          Just Refl -> vals1 === vals2
          Nothing   -> vals1 /== vals2
   , testProperty "unsafe_eq" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkUAsgn vals1
        Some y <- return $ mkUAsgn vals2
        case testEquality x y of
          Just Refl -> vals1 === vals2
          Nothing   -> vals1 /== vals2

   , testProperty "take none" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkUAsgn vals1
        Some x <- return $ mkUAsgn vals2
        Some y <- return $ mkUAsgn vals3
        let z = w U.<++> x U.<++> y
        case P.leftId z of
          Refl -> let r = C.take U.zeroSize (U.size z) z in
                    assert $ isJust $ testEquality U.empty r
   , testProperty "drop none" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkUAsgn vals1
        Some x <- return $ mkUAsgn vals2
        Some y <- return $ mkUAsgn vals3
        let z = w U.<++> x U.<++> y
        case P.leftId z of
          Refl -> let r = C.drop U.zeroSize (U.size z) z in
                    assert $ isJust $ testEquality z r
   , testProperty "take all" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkUAsgn vals1
        Some x <- return $ mkUAsgn vals2
        Some y <- return $ mkUAsgn vals3
        let z = w U.<++> x U.<++> y
        let r = C.take (U.size z) U.zeroSize z
        assert $ isJust $ testEquality z r
   , testProperty "drop all" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkUAsgn vals1
        Some x <- return $ mkUAsgn vals2
        Some y <- return $ mkUAsgn vals3
        let z = w U.<++> x U.<++> y
        let r = C.drop (U.size z) U.zeroSize z
        assert $ isJust $ testEquality U.empty r
   , testProperty "append_take" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkUAsgn vals1
        Some y <- return $ mkUAsgn vals2
        let z = x U.<++> y
        let x' = C.take (U.size x) (U.size y) z
        assert $ isJust $ testEquality x x'
   , testProperty "append_take_drop" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkUAsgn vals1
        Some y <- return $ mkUAsgn vals2
        let z = x U.<++> y
        let x' = C.take (U.size x) (U.size y) z
        let y' = C.drop (U.size x) (U.size y) z
        assert $ isJust $ testEquality x x'
        assert $ isJust $ testEquality y y'
   , testProperty "append_take_drop_multiple" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        vals4 <- forAll genSomePayloadList
        vals5 <- forAll genSomePayloadList
        Some u <- return $ mkUAsgn vals1
        Some v <- return $ mkUAsgn vals2
        Some w <- return $ mkUAsgn vals3
        Some x <- return $ mkUAsgn vals4
        Some y <- return $ mkUAsgn vals5
        let uv = u U.<++> v
        let wxy = w U.<++> x U.<++> y
        -- let z = u C.<++> v C.<++> w C.<++> x C.<++> y
        let z = uv U.<++> wxy
        let uv' = C.take (U.size uv) (U.size wxy) z
        let wxy' = C.drop (U.size uv) (U.size wxy) z
        let withWXY = C.dropPrefix z uv (error "failed dropPrefix")
        assert $ isJust $ testEquality (u U.<++> v) uv'
        assert $ isJust $ testEquality (w U.<++> x U.<++> y) wxy'
        assert $ isJust $ testEquality uv uv'
        assert $ isJust $ testEquality wxy wxy'
        withWXY $ \t -> assert $ isJust $ testEquality wxy' t
   ]
