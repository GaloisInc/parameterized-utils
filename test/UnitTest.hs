import Test.Tasty
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML

import qualified Test.Context
import qualified Test.NatRepr
import qualified Test.Vector

main :: IO ()
main = tests >>= defaultMainWithIngredients ingrs

ingrs :: [Ingredient]
ingrs =
   [ antXMLRunner
   ]
   ++
   defaultIngredients

tests :: IO TestTree
tests = testGroup "ParameterizedUtils" <$> sequence
  [ Test.Context.contextTests
  , Test.NatRepr.natTests
  , Test.Vector.vecTests
  ]
