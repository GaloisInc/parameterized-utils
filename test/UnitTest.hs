import Test.Tasty
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML

import qualified Test.Context
import qualified Test.List
import qualified Test.NatRepr
import qualified Test.SymbolRepr
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
  , pure Test.List.tests
  , Test.NatRepr.natTests
  , Test.SymbolRepr.symbolTests
  , Test.Vector.vecTests
  ]
