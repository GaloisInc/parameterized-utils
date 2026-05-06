{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Test.SmallArrayF
  ( smallArrayFTests
  ) where

import           Data.Functor.Identity (Identity(Identity, runIdentity))
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.SmallArrayF as SAF
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Parameterized.TraversableFC.WithIndex
import           Hedgehog
import qualified Hedgehog.Gen as HG
import           Hedgehog.Range (linear)
import qualified Test.Tasty as TT
import           Test.Tasty.Hedgehog

import           Test.Context (genSomePayloadList)

----------------------------------------------------------------------
-- Helpers

-- Build a SmallArrayF from a list of Some values by going through
-- Assignment.
mkSAF :: [Some f] -> Some (SAF.SmallArrayF f)
mkSAF vals =
  case go Ctx.empty vals of
    Some a -> Some (SAF.fromAssignment a)
  where
    go :: Ctx.Assignment f ctx -> [Some f] -> Some (Ctx.Assignment f)
    go acc []            = Some acc
    go acc (Some x : xs) = go (Ctx.extend acc x) xs

----------------------------------------------------------------------
-- Properties

prop_size :: Property
prop_size = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  length vals === Ctx.sizeInt (SAF.size a)

prop_indexEq :: Property
prop_indexEq = property $ do
  vals <- forAll genSomePayloadList
  i    <- forAll $ HG.int (linear 0 (length vals - 1))
  Some a <- return $ mkSAF vals
  Just (Some idx) <- return $ Ctx.intIndex i (SAF.size a)
  Some (a SAF.! idx) === vals !! i

prop_toListFC :: Property
prop_toListFC = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  vals === toListFC Some a

prop_updateRoundtrip :: Property
prop_updateRoundtrip = property $ do
  vals <- forAll genSomePayloadList
  i    <- forAll $ HG.int (linear 0 (length vals - 1))
  Some a <- return $ mkSAF vals
  Just (Some idx) <- return $ Ctx.intIndex i (SAF.size a)
  let old = a SAF.! idx
      a'  = SAF.update idx old a
  toListFC Some a === toListFC Some a'

prop_generateIndexConsistent :: Property
prop_generateIndexConsistent = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  let a' = SAF.generate (SAF.size a) (a SAF.!)
  toListFC Some a === toListFC Some a'

prop_extendSize :: Property
prop_extendSize = property $ do
  vals <- forAll genSomePayloadList
  -- Take first element of vals (guaranteed non-empty) and reuse it so
  -- we don't need a second generator.
  case vals of
    []         -> error "genSomePayloadList produced empty list"
    Some v : _ -> do
      Some a <- return $ mkSAF vals
      let a'  = SAF.extend a v
          lst = toListFC Some a'
      length lst === length vals + 1

prop_traverseFCIdentity :: Property
prop_traverseFCIdentity = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  let a' = runIdentity (traverseFC Identity a)
  toListFC Some a === toListFC Some a'

prop_foldMapFCList :: Property
prop_foldMapFCList = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  vals === foldMapFC (\x -> [Some x]) a

prop_agreesWithAssignment :: Property
prop_agreesWithAssignment = property $ do
  vals <- forAll genSomePayloadList
  i    <- forAll $ HG.int (linear 0 (length vals - 1))
  Some a <- return $ mkSAF vals
  let asgn = SAF.toAssignment a
  Just (Some idx) <- return $ Ctx.intIndex i (SAF.size a)
  Some (a SAF.! idx) === Some (asgn Ctx.! idx)

prop_imapFCConstFmap :: Property
prop_imapFCConstFmap = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  toListFC Some (imapFC (\_ x -> x) a) === toListFC Some a

prop_itraverseFCAgreesWithItoList :: Property
prop_itraverseFCAgreesWithItoList = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  let viaTraverse = runIdentity (itraverseFC (\_ x -> Identity x) a)
  toListFC Some viaTraverse === toListFC Some a

prop_ifoldMapFCFoldMapFC :: Property
prop_ifoldMapFCFoldMapFC = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  foldMapFC (\x -> [Some x]) a === ifoldMapFC (\_ x -> [Some x]) a

-- zipWithFC id is fmapFC (given equal inputs)
prop_zipWithFCDiag :: Property
prop_zipWithFCDiag = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  toListFC Some (SAF.zipWithFC (\x _ -> x) a a) === toListFC Some a

-- zipWithMFC with Identity agrees with zipWithFC
prop_zipWithMFCAgreesWithZipWithFC :: Property
prop_zipWithMFCAgreesWithZipWithFC = property $ do
  vals <- forAll genSomePayloadList
  Some a <- return $ mkSAF vals
  let pure' = SAF.zipWithFC (\x _ -> x) a a
      eff   = runIdentity (SAF.zipWithMFC (\x _ -> Identity x) a a)
  toListFC Some pure' === toListFC Some eff

-- append produces the concatenation of both element lists
prop_appendConcat :: Property
prop_appendConcat = property $ do
  xs <- forAll genSomePayloadList
  ys <- forAll genSomePayloadList
  Some a <- return $ mkSAF xs
  Some b <- return $ mkSAF ys
  toListFC Some (SAF.append a b) === (xs ++ ys)

-- unextend is the inverse of extend
prop_unextendExtend :: Property
prop_unextendExtend = property $ do
  vals <- forAll genSomePayloadList
  Some v : _ <- return vals
  Some a <- return $ mkSAF vals
  let a' = SAF.extend a v
      (a'', v') = SAF.unextend a'
  toListFC Some a === toListFC Some a''
  Some v === Some v'

-- take and drop partition append
prop_takeDropPartition :: Property
prop_takeDropPartition = property $ do
  xs <- forAll genSomePayloadList
  ys <- forAll genSomePayloadList
  Some a <- return $ mkSAF xs
  Some b <- return $ mkSAF ys
  let ab = SAF.append a b
      sa = SAF.size a
      sb = SAF.size b
  toListFC Some (SAF.take sa sb ab) ++ toListFC Some (SAF.drop sa sb ab)
    === toListFC Some ab

----------------------------------------------------------------------

smallArrayFTests :: IO TT.TestTree
smallArrayFTests = return $ TT.testGroup "SmallArrayF"
  [ testPropertyNamed "size" "prop_size" prop_size
  , testPropertyNamed "index_eq" "prop_indexEq" prop_indexEq
  , testPropertyNamed "toListFC" "prop_toListFC" prop_toListFC
  , testPropertyNamed "update_roundtrip" "prop_updateRoundtrip" prop_updateRoundtrip
  , testPropertyNamed "generate_index_consistent" "prop_generateIndexConsistent" prop_generateIndexConsistent
  , testPropertyNamed "extend_size" "prop_extendSize" prop_extendSize
  , testPropertyNamed "traverseFC_identity" "prop_traverseFCIdentity" prop_traverseFCIdentity
  , testPropertyNamed "foldMapFC_list" "prop_foldMapFCList" prop_foldMapFCList
  , testPropertyNamed "agrees_with_assignment" "prop_agreesWithAssignment" prop_agreesWithAssignment
  , testPropertyNamed "imapFC_const_fmap" "prop_imapFCConstFmap" prop_imapFCConstFmap
  , testPropertyNamed "itraverseFC_identity" "prop_itraverseFCAgreesWithItoList" prop_itraverseFCAgreesWithItoList
  , testPropertyNamed "ifoldMapFC_foldMapFC" "prop_ifoldMapFCFoldMapFC" prop_ifoldMapFCFoldMapFC
  , testPropertyNamed "zipWithFC_diag" "prop_zipWithFCDiag" prop_zipWithFCDiag
  , testPropertyNamed "zipWithMFC_agrees_zipWithFC" "prop_zipWithMFCAgreesWithZipWithFC" prop_zipWithMFCAgreesWithZipWithFC
  , testPropertyNamed "append_concat" "prop_appendConcat" prop_appendConcat
  , testPropertyNamed "unextend_extend" "prop_unextendExtend" prop_unextendExtend
  , testPropertyNamed "take_drop_partition" "prop_takeDropPartition" prop_takeDropPartition
  ]
