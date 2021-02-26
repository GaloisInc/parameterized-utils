{-# LANGUAGE TypeApplications #-}
{-# Language CPP #-}
{-# Language DataKinds #-}
{-# Language ExplicitForAll #-}
{-# Language FlexibleInstances #-}
{-# Language LambdaCase #-}
{-# Language ScopedTypeVariables #-}
{-# Language StandaloneDeriving #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
#if __GLASGOW_HASKELL__ >= 805
{-# Language NoStarIsType #-}
#endif
module Test.Vector
  ( vecTests
  )
where

import           Data.Functor.Const (Const(..))
import           Data.Maybe (isJust)
import qualified Data.List as List
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import           Data.Parameterized.Vector
import           Data.Semigroup
import           GHC.TypeLits
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range
import           Prelude hiding (take, reverse)
import qualified Prelude as P
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Context (genSomePayloadList, mkUAsgn)


genVector :: (1 <= n, KnownNat n, Monad m) => GenT m a -> GenT m (Vector n a)
genVector genElem =
  do let n = knownNat
         w = widthVal n
     l <- HG.list (constant w w) genElem
     case fromList n l of
       Just v -> return v
       Nothing -> error ("fromList failure for size " <> show w)

genOrdering :: Monad m => GenT m Ordering
genOrdering = HG.element [ LT, EQ, GT ]


instance Show (a -> b) where
  show _ = "unshowable"


-- We use @Ordering@ just because it's simple
vecTests :: IO TestTree
vecTests = testGroup "Vector" <$> return
  [ testProperty "reverse100" $ property $
    do v <- forAll $ genVector @100 genOrdering
       v === (reverse $ reverse v)
  , testProperty "reverseSingleton" $ property $
    do l <- (:[]) <$> forAll genOrdering
       Just v <- return $ fromList (knownNat @1) l
       v === reverse v

  , testProperty "split-join" $ property $
    do let n = knownNat @5
       v <- forAll $ genVector @(5 * 5) genOrdering
       v === (join n $ split n (knownNat @5) v)

  -- @cons@ is the same for vectors or lists
  , testProperty "cons" $ property $
    do let n = knownNat @20
           w = widthVal n
       l <- forAll $ HG.list (constant w w) genOrdering
       x <- forAll genOrdering
       (cons x <$> fromList n l) === fromList (incNat n) (x:l)

  -- @snoc@ is like appending to a list
  , testProperty "snoc" $ property $
    do let n = knownNat @20
           w = widthVal n
       l <- forAll $ HG.list (constant w w) genOrdering
       x <- forAll genOrdering
       (flip snoc x <$> fromList n l) === fromList (incNat n) (l ++ [x])

  -- @snoc@ and @unsnoc@ are inverses
  , testProperty "snoc/unsnoc" $ property $
    do let n = knownNat @20
           w = widthVal n
       l <- forAll $ HG.list (constant w w) genOrdering
       x <- forAll genOrdering
       (fst  . unsnoc . flip snoc x <$> fromList n l) === Just x

  -- @generate@ is like mapping a function over indices
  , testProperty "generate" $ property $
    do let n = knownNat @55
           w = widthVal n
           funs :: [ Int -> Ordering ]  -- some miscellaneous functions to generate Vector values
           funs =  [ const EQ
                   , \i -> if i < 10 then LT else if i > 15 then GT else EQ
                   , \i -> if i == 0 then EQ else GT
                   ]
       f <- forAll $ HG.element funs
       Just (generate n (f . widthVal)) === fromList (incNat n) (map f [0..w])

  -- @unfold@ works like @unfold@ on lists
  , testProperty "unfold" $ property $
    do let n = knownNat @55
           w = widthVal n
           funs :: [ Ordering -> (Ordering, Ordering) ]  -- some miscellaneous functions to generate Vector values
           funs =  [ const (EQ, EQ)
                   , \case
                       LT -> (LT, GT)
                       GT -> (GT, LT)
                       EQ -> (EQ, EQ)
                   ]
       f <- forAll $ HG.element funs
       o <- forAll $ HG.element [EQ, LT, GT]
       Just (unfoldr n f o) === fromList (incNat n) (P.take (w + 1) (List.unfoldr (Just . f) o))

  -- Converting to and from assignments preserves size and last element
  , testProperty "to-from-assignment" $ property $
    do vals <- forAll genSomePayloadList
       Some a <- return $ mkUAsgn vals
       let sz = Ctx.size a
       case Ctx.viewSize sz of
         Ctx.ZeroSize -> pure ()
         Ctx.IncSize _ ->
           let a' =
                 toAssignment
                   sz
                   (\_idx val -> Const val)
                   (fromAssignment Some a)
           in do assert $
                   isJust $
                     testEquality
                       (Ctx.sizeToNatRepr sz)
                       (Ctx.sizeToNatRepr (Ctx.size a'))
                 viewSome
                   (\lastElem ->
                      assert $
                        isJust $
                          testEquality
                            (a Ctx.! Ctx.lastIndex sz) lastElem)
                   (getConst (a' Ctx.! Ctx.lastIndex sz))
    ]
