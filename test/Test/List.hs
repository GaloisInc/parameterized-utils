module Test.List
  ( tests
  ) where

import           Control.Monad.Identity
import           Data.Functor.Const
import qualified Data.Parameterized.List as PL
import           Data.Parameterized.Some
import           Test.Tasty
import           Test.Tasty.HUnit

-- | Test ifoldlM indexing is correct by summing a list using it.
testIfoldlMSum :: [Integer] -> TestTree
testIfoldlMSum l =
  testCase ("ifoldlMSum " ++ show l) $
    case PL.fromListWith (Some . Const) l of
      Some pl ->
        let expected = sum l
            actual = PL.ifoldlM (\r i v -> Identity $ r + if pl PL.!! i == v then getConst v else 0) 0 pl
        in expected @?= runIdentity actual


tests :: TestTree
tests = testGroup "List"
  [ testIfoldlMSum []
  , testIfoldlMSum [1]
  , testIfoldlMSum [1,2]
  , testIfoldlMSum [1,2,3]
  ]