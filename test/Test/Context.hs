{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Test.Context
  ( contextTests
  )
where

import           Control.Lens
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as C
import qualified Data.Parameterized.Ctx.Proofs as P
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


type Asgn = C.Assignment Payload

mkAsgn :: [Some Payload] -> Some Asgn
mkAsgn = go C.empty
 where go :: Asgn ctx -> [Some Payload] -> Some Asgn
       go a [] = Some a
       go a (Some x : xs) = go (C.extend a x) xs


twiddle :: Payload a -> Payload a
twiddle (IntPayload n) = IntPayload (n+1)
twiddle (StringPayload str) = StringPayload (str++"asdf")
twiddle (BoolPayload b) = BoolPayload (not b)

grpName :: String
#ifdef UNSAFE_OPS
grpName = "Unsafe Context"
#else
grpName = "Safe Context"
#endif

contextTests :: IO TestTree
contextTests = testGroup grpName <$> return
   [ testProperty "index_eq" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)
        Some a <- return $ mkAsgn vals
        Just (Some idx) <- return $ C.intIndex i' (C.size a)
        Some (a C.! idx) === vals !! i'

   , testProperty "tolist" $ property $
     do vals <- forAll genSomePayloadList
        Some a <- return $ mkAsgn vals
        let vals' = toListFC Some a
        vals === vals'

   , testProperty "adjust test monadic" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)

        Some x <- return $ mkAsgn vals
        Some y <- return $ mkAsgn vals
        Some z <- return $ mkAsgn vals

        Just (Some idx_x) <- return $ C.intIndex i' (C.size x)
        Just (Some idx_y) <- return $ C.intIndex i' (C.size y)

        x' <- C.adjustM (return . twiddle) idx_x x
        y' <- C.adjustM (return . twiddle) idx_y y

        toListFC Some x  === toListFC Some z
        toListFC Some y  === toListFC Some z
        toListFC Some z  === toListFC Some z
        toListFC Some x' /== toListFC Some x
        toListFC Some y' /== toListFC Some y
        toListFC Some x' === toListFC Some y'

   , testProperty "adjust test lensed" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)

        Some x <- return $ mkAsgn vals
        Some y <- return $ mkAsgn vals
        Some z <- return $ mkAsgn vals

        Just (Some idx_x) <- return $ C.intIndex i' (C.size x)
        Just (Some idx_y) <- return $ C.intIndex i' (C.size y)

        let x' = x & ixF idx_x %~ twiddle
            y' = y & ixF idx_y %~ twiddle

        toListFC Some x  === toListFC Some z
        toListFC Some y  === toListFC Some z
        toListFC Some z  === toListFC Some z
        toListFC Some x' /== toListFC Some x
        toListFC Some y' /== toListFC Some y
        toListFC Some x' === toListFC Some y'

   , testProperty "update test" $ property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)

        Some x <- return $ mkAsgn vals
        Some y <- return $ mkAsgn vals

        Just (Some idx_x) <- return $ C.intIndex i' (C.size x)
        Just (Some idx_y) <- return $ C.intIndex i' (C.size y)

        let x' = over (ixF idx_x) twiddle x
            y' = (ixF idx_y) %~ twiddle $ y
            updX = x & ixF idx_x .~ x' C.! idx_x
            updY = y & ixF idx_y .~ y' C.! idx_y

        toListFC Some updX === toListFC Some updY
        -- update actually modified the entry
        toListFC Some x /== toListFC Some updX
        toListFC Some y /== toListFC Some updY
        -- update modified the expected entry
        toListFC Some x' === toListFC Some updX
        toListFC Some y' === toListFC Some updY

   , testProperty "testEquality" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkAsgn vals1
        Some y <- return $ mkAsgn vals2
        case testEquality x y of
          Just Refl -> vals1 === vals2
          Nothing   -> vals1 /== vals2

   , testProperty "take none" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkAsgn vals1
        Some x <- return $ mkAsgn vals2
        Some y <- return $ mkAsgn vals3
        let z = w C.<++> x C.<++> y
        case P.leftId z of
          Refl -> let r = C.take C.zeroSize (C.size z) z in
                    assert $ isJust $ testEquality C.empty r
   , testProperty "drop none" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkAsgn vals1
        Some x <- return $ mkAsgn vals2
        Some y <- return $ mkAsgn vals3
        let z = w C.<++> x C.<++> y
        case P.leftId z of
          Refl -> let r = C.drop C.zeroSize (C.size z) z in
                    assert $ isJust $ testEquality z r
   , testProperty "take all" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkAsgn vals1
        Some x <- return $ mkAsgn vals2
        Some y <- return $ mkAsgn vals3
        let z = w C.<++> x C.<++> y
        let r = C.take (C.size z) C.zeroSize z
        assert $ isJust $ testEquality z r
   , testProperty "drop all" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        Some w <- return $ mkAsgn vals1
        Some x <- return $ mkAsgn vals2
        Some y <- return $ mkAsgn vals3
        let z = w C.<++> x C.<++> y
        let r = C.drop (C.size z) C.zeroSize z
        assert $ isJust $ testEquality C.empty r
   , testProperty "append_take" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkAsgn vals1
        Some y <- return $ mkAsgn vals2
        let z = x C.<++> y
        let x' = C.take (C.size x) (C.size y) z
        assert $ isJust $ testEquality x x'
   , testProperty "append_take_drop" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkAsgn vals1
        Some y <- return $ mkAsgn vals2
        let z = x C.<++> y
        let x' = C.take (C.size x) (C.size y) z
        let y' = C.drop (C.size x) (C.size y) z
        assert $ isJust $ testEquality x x'
        assert $ isJust $ testEquality y y'

   , testProperty "append_take_drop 2" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        Some x <- return $ mkAsgn vals1
        Some y <- return $ mkAsgn vals2
        let z = x C.<++> y
        let x' = C.take (C.size x) (C.size y) z
        let y' = C.drop (C.size x) (C.size y) z
        let withYTail = C.dropPrefix z x (error "failed dropPrefix")
        -- let yt = C.dropPrefix z x (error "failed dropPrefix") (\t -> t)
        assert $ isJust $ testEquality x x'
        assert $ isJust $ testEquality y y'
        withYTail $ \t -> assert $ isJust $ testEquality y t
        -- assert $ isJust $ testEquality y yt

   , testProperty "append_take_drop_multiple" $ property $
     do vals1 <- forAll genSomePayloadList
        vals2 <- forAll genSomePayloadList
        vals3 <- forAll genSomePayloadList
        vals4 <- forAll genSomePayloadList
        vals5 <- forAll genSomePayloadList
        Some u <- return $ mkAsgn vals1
        Some v <- return $ mkAsgn vals2
        Some w <- return $ mkAsgn vals3
        Some x <- return $ mkAsgn vals4
        Some y <- return $ mkAsgn vals5
        let uv = u C.<++> v
        let wxy = w C.<++> x C.<++> y
        -- let z = u C.<++> v C.<++> w C.<++> x C.<++> y
        let z = uv C.<++> wxy
        let uv' = C.take (C.size uv) (C.size wxy) z
        let wxy' = C.drop (C.size uv) (C.size wxy) z
        let withWXY = C.dropPrefix z uv (error "failed dropPrefix")
        assert $ isJust $ testEquality (u C.<++> v) uv'
        assert $ isJust $ testEquality (w C.<++> x C.<++> y) wxy'
        assert $ isJust $ testEquality uv uv'
        assert $ isJust $ testEquality wxy wxy'
        withWXY $ \t -> assert $ isJust $ testEquality wxy' t
   ]
