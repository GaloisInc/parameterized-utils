{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Test.Context
  ( contextTests
  , genSomePayloadList
  , mkUAsgn
  , mkSAsgn
  )
where

import           Data.Function ((&))
import           Data.Functor.Identity (Identity(..))
import           Data.Functor.Product (Product(Pair))
import           Data.Kind
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as C
import qualified Data.Parameterized.Context.Safe as S
import qualified Data.Parameterized.Context.Unsafe as U
import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Ctx.Proofs as P
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.TraversableFC.WithIndex
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range
import           Lens.Micro ((%~), (.~), over)
import           Test.Tasty
import           Test.Tasty.HUnit ( (@=?), (@?=), testCaseSteps )
import           Test.Tasty.Hedgehog

----------------------------------------------------------------------
-- Create a Payload GADT which is the parameterized type used for many
-- of the Context/Assignment tests in this module.

data Payload (ty :: Type) where
  IntPayload    :: Int -> Payload Int
  StringPayload :: String -> Payload String
  BoolPayload   :: Bool -> Payload Bool

deriving instance Eq (Payload ty)

instance TestEquality Payload where
  testEquality (IntPayload x) (IntPayload y) = if x == y then Just Refl else Nothing
  testEquality (StringPayload x) (StringPayload y) = if x == y then Just Refl else Nothing
  testEquality (BoolPayload x) (BoolPayload y) = if x == y then Just Refl else Nothing
  testEquality _ _ = Nothing

instance Show (Payload tp) where
  show (IntPayload x) = show x <> " :: Int"
  show (StringPayload x) = show x <> " :: String"
  show (BoolPayload x) = show x <> " :: Bool"

instance ShowF Payload

twiddle :: Payload a -> Payload a
twiddle (IntPayload n) = IntPayload (n+1)
twiddle (StringPayload str) = StringPayload (str++"asdf")
twiddle (BoolPayload b) = BoolPayload (not b)

twaddle :: Payload a -> Payload a
twaddle (IntPayload n) = IntPayload (n-1)
twaddle (StringPayload str) = StringPayload (reverse str)
twaddle (BoolPayload b) = BoolPayload (not b)

newtype Fun = Fun (forall a. Payload a -> Payload a)

instance Show Fun where
  show _ = "unshowable"

-- | Functions for e.g. testing functor laws
funs :: [Fun]
funs = [Fun twiddle, Fun twaddle, Fun id]

----------------------------------------------------------------------
-- Create another parameterized type for testing.  This one is not a
-- GADT, which will require some interesting implementation tricks.
--
-- The common 'Maybe' type is potentially useable for this type, but
-- there are some restrictions on 'Maybe'.  For example, it is not
-- possible to create a @ShowF Maybe@ because although 'Maybe' is of type
-- @(k -> type)@, @k@ is unconstrained and doesn't contain a 'Show'
-- constraint.

data MyMaybe t = (Show t) => MyJust t | MyNothing
instance ShowF MyMaybe
instance Show (MyMaybe t) where
  show (MyJust x) = "MyJust " <> show x
  show MyNothing = "MyNothing"

----------------------------------------------------------------------
-- Some Hedgehog generators

genSomePayload :: Monad m => GenT m (Some Payload)
genSomePayload =
  HG.choice
  [ Some . IntPayload    <$> HG.integral (linearBounded :: Range Int)
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

----------------------------------------------------------------------
-- A Ctx type that will be used for some of the Assignments tested here

type TestCtx = U.EmptyCtx '::> Int '::> String '::> Int '::> Bool

----------------------------------------------------------------------
-- Hedgehog properties

prop_sizeUnsafe :: Property
prop_sizeUnsafe = property $
  do vals <- forAll genSomePayloadList
     Some a <- return $ mkUAsgn vals
     length vals === U.sizeInt (U.size a)

prop_sizeSafe :: Property
prop_sizeSafe = property $
  do vals <- forAll genSomePayloadList
     Some a <- return $ mkSAsgn vals
     length vals === S.sizeInt (S.size a)

prop_safeIndexEq :: Property
prop_safeIndexEq = property $
     do vals <- forAll genSomePayloadList
        i' <- forAll $ HG.int (linear 0 $ length vals - 1)
        Some a <- return $ mkSAsgn vals
        Just (Some idx) <- return $ S.intIndex i' (S.size a)
        Some (a S.! idx) === vals !! i'

prop_unsafeIndexEq :: Property
prop_unsafeIndexEq = property $
  do vals <- forAll genSomePayloadList
     i' <- forAll $ HG.int (linear 0 $ length vals - 1)
     Some a <- return $ mkUAsgn vals
     Just (Some idx) <- return $ U.intIndex i' (U.size a)
     Some (a U.! idx) === vals !! i'

prop_safeToList :: Property
prop_safeToList = property $
  do vals <- forAll genSomePayloadList
     Some a <- return $ mkSAsgn vals
     let vals' = toListFC Some a
     vals === vals'

prop_unsafeToList :: Property
prop_unsafeToList = property $
  do vals <- forAll genSomePayloadList
     Some a <- return $ mkUAsgn vals
     let vals' = toListFC Some a
     vals === vals'

prop_adjustTestMonadic :: Property
prop_adjustTestMonadic = property $
  do vals <- forAll genSomePayloadList
     i' <- forAll $ HG.int (linear 0 $ length vals - 1)

     Some x <- return $ mkUAsgn vals
     Some y <- return $ mkSAsgn vals

     Just (Some idx_x) <- return $ U.intIndex i' (U.size x)
     Just (Some idx_y) <- return $ S.intIndex i' (S.size y)

     x' <- U.adjustM (return . twiddle) idx_x x
     y' <- S.adjustM (return . twiddle) idx_y y

     toListFC Some x' === toListFC Some y'

prop_adjustTest :: Property
prop_adjustTest = property $
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

prop_updateTest :: Property
prop_updateTest = property $
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

prop_safeEq :: Property
prop_safeEq = property $
  do vals1 <- forAll genSomePayloadList
     vals2 <- forAll genSomePayloadList
     Some x <- return $ mkSAsgn vals1
     Some y <- return $ mkSAsgn vals2
     case testEquality x y of
       Just Refl -> vals1 === vals2
       Nothing   -> vals1 /== vals2

prop_unsafeEq :: Property
prop_unsafeEq = property $
  do vals1 <- forAll genSomePayloadList
     vals2 <- forAll genSomePayloadList
     Some x <- return $ mkUAsgn vals1
     Some y <- return $ mkUAsgn vals2
     case testEquality x y of
       Just Refl -> vals1 === vals2
       Nothing   -> vals1 /== vals2

prop_takeNone :: Property
prop_takeNone = property $
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

prop_dropNone :: Property
prop_dropNone = property $
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

prop_takeAll :: Property
prop_takeAll = property $
  do vals1 <- forAll genSomePayloadList
     vals2 <- forAll genSomePayloadList
     vals3 <- forAll genSomePayloadList
     Some w <- return $ mkUAsgn vals1
     Some x <- return $ mkUAsgn vals2
     Some y <- return $ mkUAsgn vals3
     let z = w U.<++> x U.<++> y
     let r = C.take (U.size z) U.zeroSize z
     assert $ isJust $ testEquality z r

prop_dropAll :: Property
prop_dropAll = property $
  do vals1 <- forAll genSomePayloadList
     vals2 <- forAll genSomePayloadList
     vals3 <- forAll genSomePayloadList
     Some w <- return $ mkUAsgn vals1
     Some x <- return $ mkUAsgn vals2
     Some y <- return $ mkUAsgn vals3
     let z = w U.<++> x U.<++> y
     let r = C.drop (U.size z) U.zeroSize z
     assert $ isJust $ testEquality U.empty r

prop_appendTake :: Property
prop_appendTake = property $
  do vals1 <- forAll genSomePayloadList
     vals2 <- forAll genSomePayloadList
     Some x <- return $ mkUAsgn vals1
     Some y <- return $ mkUAsgn vals2
     let z = x U.<++> y
     let x' = C.take (U.size x) (U.size y) z
     assert $ isJust $ testEquality x x'

prop_appendTakeDrop :: Property
prop_appendTakeDrop = property $
  do vals1 <- forAll genSomePayloadList
     vals2 <- forAll genSomePayloadList
     Some x <- return $ mkUAsgn vals1
     Some y <- return $ mkUAsgn vals2
     let z = x U.<++> y
     let x' = C.take (U.size x) (U.size y) z
     let y' = C.drop (U.size x) (U.size y) z
     assert $ isJust $ testEquality x x'
     assert $ isJust $ testEquality y y'

prop_appendTakeDropMultiple :: Property
prop_appendTakeDropMultiple = property $
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

prop_zipUnzip :: Property
prop_zipUnzip = property $
  do Some x <- mkUAsgn <$> forAll genSomePayloadList
     let zipped = C.zipWith Pair x x
     let (x', x'') = C.unzip zipped
     assert $ isJust $ testEquality x x'
     assert $ isJust $ testEquality x x''

prop_fmapFCIdentity :: Property
prop_fmapFCIdentity = property $
  do Some x <- mkUAsgn <$> forAll genSomePayloadList
     assert $ isJust $ testEquality x (fmapFC id x)

prop_fmapFCAssoc :: Property
prop_fmapFCAssoc = property $
  do Some x <- mkUAsgn <$> forAll genSomePayloadList
     Fun f <- forAll $ HG.element funs
     Fun g <- forAll $ HG.element funs
     assert $ isJust $ testEquality
                         (fmapFC g (fmapFC f x))
                         (fmapFC (g . f) x)

prop_imapFCIndexNoop :: Property
prop_imapFCIndexNoop = property $
  do Some x <- mkUAsgn <$> forAll genSomePayloadList
     assert $
       isJust $
         testEquality x (imapFC (\idx _ -> x U.! idx) x)

prop_imapFCFmapFC :: Property
prop_imapFCFmapFC = property $
  do Some x <- mkUAsgn <$> forAll genSomePayloadList
     Fun f <- forAll $ HG.element funs
     assert $ isJust $ testEquality
                         (fmapFC f x)
                         (imapFC (const f) x)

prop_ifoldMapFCFoldMapFC :: Property
prop_ifoldMapFCFoldMapFC = property $
  do Some x <- mkUAsgn <$> forAll genSomePayloadList
     assert $ foldMapFC show x == ifoldMapFC (const show) x

prop_itraverseFCTraverseFC :: Property
prop_itraverseFCTraverseFC = property $
  do Some x <- mkUAsgn <$> forAll genSomePayloadList
     Fun f <- forAll $ HG.element funs
     let f' :: forall a. Payload a -> Identity (Payload a)
         f' = Identity . f
     assert $ isJust $ testEquality
                         (runIdentity (traverseFC f' x))
                         (runIdentity (itraverseFC (const f') x))

----------------------------------------------------------------------

contextTests :: IO TestTree
contextTests = testGroup "Context" <$> return
   [ testPropertyNamed "size (unsafe)" "prop_sizeUnsafe" prop_sizeUnsafe
   , testPropertyNamed "size (safe)" "prop_sizeSafe" prop_sizeSafe

   , testPropertyNamed "safe_index_eq" "prop_safeIndexEq" prop_safeIndexEq

   , testPropertyNamed "unsafe_index_eq" "prop_unsafeIndexEq" prop_unsafeIndexEq

   , testPropertyNamed "safe_tolist" "prop_safeToList" prop_safeToList
   , testPropertyNamed "unsafe_tolist" "prop_unsafeToList" prop_unsafeToList

   , testPropertyNamed "adjust test monadic" "prop_adjustTestMonadic" prop_adjustTestMonadic

   , testPropertyNamed "adjust test" "prop_adjustTest" prop_adjustTest

   , testPropertyNamed "update test" "prop_updateTest" prop_updateTest

   , testPropertyNamed "safe_eq" "prop_safeEq" prop_safeEq
   , testPropertyNamed "unsafe_eq" "prop_unsafeEq" prop_unsafeEq

   , testPropertyNamed "take none" "prop_takeNone" prop_takeNone
   , testPropertyNamed "drop none" "prop_dropNone" prop_dropNone

   , testPropertyNamed "take all" "prop_takeAll" prop_takeAll
   , testPropertyNamed "drop all" "prop_dropAll" prop_dropAll

   , testPropertyNamed "append_take" "prop_appendTake" prop_appendTake

   , testPropertyNamed "append_take_drop" "prop_appendTakeDrop" prop_appendTakeDrop

   , testPropertyNamed "append_take_drop_multiple" "prop_appendTakeDropMultiple" prop_appendTakeDropMultiple

   , testPropertyNamed "zip/unzip" "prop_zipUnzip" prop_zipUnzip

   , testPropertyNamed "fmapFC_identity" "prop_fmapFCIdentity" prop_fmapFCIdentity

   , testPropertyNamed "fmapFC_assoc" "prop_fmapFCAssoc" prop_fmapFCAssoc

   , testPropertyNamed "imapFC_index_noop" "prop_imapFCIndexNoop" prop_imapFCIndexNoop

   , testPropertyNamed "imapFC/fmapFC" "prop_imapFCFmapFC" prop_imapFCFmapFC

   , testPropertyNamed "ifoldMapFC/foldMapFC" "prop_ifoldMapFCFoldMapFC" prop_ifoldMapFCFoldMapFC

   , testPropertyNamed "itraverseFC/traverseFC" "prop_itraverseFCTraverseFC" prop_itraverseFCTraverseFC

   , testCaseSteps "explicit indexing (unsafe)" $ \step -> do
       let mkUPayload :: U.Assignment Payload TestCtx
           mkUPayload = U.empty
                        `U.extend` IntPayload 1
                        `U.extend` StringPayload "two"
                        `U.extend` IntPayload 3
                        `U.extend` BoolPayload True

           -- Alternative construction using the 'generate' and a
           -- function consuming @Index ctx tp@ selectors to return
           -- the corresponding value
           mkUMyMaybe :: U.Assignment MyMaybe TestCtx
           mkUMyMaybe = U.generate U.knownSize setMyValue
           setMyValue :: U.Index TestCtx tp -> MyMaybe tp
           setMyValue idx
             | Just Refl <- testEquality (U.lastIndex U.knownSize) idx
             = MyJust False
             | Just Refl <- testEquality (U.skipIndex $ U.skipIndex $ U.skipIndex U.baseIndex) idx
             = MyJust 10
             | Just Refl <- testEquality (U.skipIndex $ U.skipIndex $ U.nextIndex U.knownSize) idx
             = MyJust "twenty"
             | Just Refl <- testEquality (U.skipIndex $ U.nextIndex U.knownSize) idx
             = MyNothing
             | otherwise = error $ "setMyValue with unrecognized Index " <> show idx

       step "Verify size of Assignment"
       U.sizeInt (U.size mkUPayload) @?= 4

       step "Verify show of Assignment"
       "[1 :: Int, \"two\" :: String, 3 :: Int, True :: Bool]" @=? show mkUPayload
       "[MyJust 10, MyJust \"twenty\", MyNothing, MyJust False]" @=? show mkUMyMaybe

       step "Verify show explicit indexing"
       Just "\"two\" :: String" @=?
         do Some i <- U.intIndex 1 (U.size mkUPayload)
            return $ show $ mkUPayload U.! i
       Just "1 :: Int" @=?
         do Some i <- U.intIndex 0 (U.size mkUPayload)
            return $ show $ mkUPayload U.! i
       "#<; @0=1 :: Int; @1=\"two\" :: String; @2=3 :: Int; @3=True :: Bool" @=?
         U.forIndex U.knownSize
         (\s idx -> s <> "; @" <> show idx <> "=" <>
                    show (mkUPayload U.! idx))
         "#<"
       (Nothing @String) @=?
         do Some i <- U.intIndex 8 (U.size mkUPayload)
            return $ show $ mkUPayload U.! i

       step "Verify invalid type at index"
       (Nothing :: Maybe Bool) @=?
         do Some i <- U.intIndex 1 (U.size mkUPayload)
            Refl <- testEquality (mkUPayload U.! i) (IntPayload 1)
            return True

   , testCaseSteps "explicit indexing (safe)" $ \step -> do
       let mkSPayload :: S.Assignment Payload TestCtx
           mkSPayload = S.empty
                        `S.extend` IntPayload 1
                        `S.extend` StringPayload "two"
                        `S.extend` IntPayload 3
                        `S.extend` BoolPayload True

           -- Alternative construction using the 'generate' and a
           -- function consuming @Index ctx tp@ selectors to return
           -- the corresponding value
           mkSMyMaybe :: S.Assignment MyMaybe TestCtx
           mkSMyMaybe = S.generate S.knownSize setMyValue
           setMyValue :: S.Index TestCtx tp -> MyMaybe tp
           setMyValue idx
             | Just Refl <- testEquality (S.lastIndex S.knownSize) idx
             = MyJust False
             | Just Refl <- testEquality (S.skipIndex $ S.skipIndex $ S.skipIndex S.baseIndex) idx
             = MyJust 10
             | Just Refl <- testEquality (S.skipIndex $ S.skipIndex $ S.nextIndex S.knownSize) idx
             = MyJust "twenty"
             | Just Refl <- testEquality (S.skipIndex $ S.nextIndex S.knownSize) idx
             = MyNothing
             | otherwise = error $ "setMyValue with unrecognized Index " <> show idx

       step "Verify size of Assignment"
       S.sizeInt (S.size mkSPayload) @?= 4

       step "Verify show of Assignment"
       "[1 :: Int, \"two\" :: String, 3 :: Int, True :: Bool]" @=? show mkSPayload
       "[MyJust 10, MyJust \"twenty\", MyNothing, MyJust False]" @=? show mkSMyMaybe

       step "Verify show explicit indexing"
       Just "\"two\" :: String" @=?
         do Some i <- S.intIndex 1 (S.size mkSPayload)
            return $ show $ mkSPayload S.! i
       Just "1 :: Int" @=?
         do Some i <- S.intIndex 0 (S.size mkSPayload)
            return $ show $ mkSPayload S.! i
       "#<; @3=True :: Bool; @2=3 :: Int; @1=\"two\" :: String; @0=1 :: Int" @=?
         S.forIndex S.knownSize
         (\s idx -> s <> "; @" <> show idx <> "=" <>
                    show (mkSPayload S.! idx))
         "#<"
       (Nothing @String) @=?
         do Some i <- S.intIndex 8 (S.size mkSPayload)
            return $ show $ mkSPayload S.! i

       step "Verify invalid type at index"
       (Nothing :: Maybe Bool) @=?
         do Some i <- S.intIndex 1 (S.size mkSPayload)
            Refl <- testEquality (mkSPayload S.! i) (IntPayload 1)
            return True

   , testCaseSteps "joined Assigment operations (unsafe)" $ \step -> do
       let mkU1 = U.empty
                  `U.extend` IntPayload 1
           mkU2 = U.empty
                  `U.extend` StringPayload "two"
                  `U.extend` IntPayload 3
                  `U.extend` BoolPayload True

       step "Length"
       U.sizeInt (U.size mkU1) + U.sizeInt (U.size mkU2) @?=
         U.sizeInt (U.size (mkU1 U.<++> mkU2))

       step "Index adjustments"
       Just (Some i1) <- return $ U.intIndex 0 (U.size mkU1)
       v1s <- return $ show $ mkU1 U.! i1
       "1 :: Int" @=? v1s
       Just (Some i2) <- return $ U.intIndex 2 (U.size mkU2)
       v2s <- return $ show $ mkU2 U.! i2
       "True :: Bool" @=? v2s
       let mkUB = mkU1 U.<++> mkU2
       v1s' <- return $ show $ mkUB U.! (U.leftIndex (U.size mkU2) i1)
       v1s' @?= v1s
       v2s' <- return $ show $ mkUB U.! (U.rightIndex (U.size mkU1) (U.size mkU2) i2)
       v2s' @?= v2s

   , testCaseSteps "joined Assigment operations (safe)" $ \step -> do
       let mkS1 = S.empty
                  `S.extend` IntPayload 1
           mkS2 = S.empty
                  `S.extend` StringPayload "two"
                  `S.extend` IntPayload 3
                  `S.extend` BoolPayload True

       step "Length"
       S.sizeInt (S.size mkS1) + S.sizeInt (S.size mkS2) @?=
         S.sizeInt (S.size (mkS1 S.<++> mkS2))

       step "Index adjustments"
       Just (Some i1) <- return $ S.intIndex 0 (S.size mkS1)
       v1s <- return $ show $ mkS1 S.! i1
       "1 :: Int" @=? v1s
       Just (Some i2) <- return $ S.intIndex 2 (S.size mkS2)
       v2s <- return $ show $ mkS2 S.! i2
       "True :: Bool" @=? v2s
       let mkSB = mkS1 S.<++> mkS2
       v1s' <- return $ show $ mkSB S.! (S.leftIndex (S.size mkS2) i1)
       v1s' @?= v1s
       v2s' <- return $ show $ mkSB S.! (S.rightIndex (S.size mkS1) (S.size mkS2) i2)
       v2s' @?= v2s

   ]
