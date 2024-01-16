import Test.Tasty
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML

import qualified Test.Context
import qualified Test.Context.Elective
import qualified Test.Fin
import qualified Test.FinMap
import qualified Test.List
import qualified Test.NatRepr
import qualified Test.Some
import qualified Test.SymbolRepr
import qualified Test.TH
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
  , pure Test.Context.Elective.electiveTests
  , pure Test.List.tests
  , Test.Fin.finTests
  , Test.FinMap.finMapTests
  , Test.NatRepr.natTests
  , Test.Some.someTests
  , Test.SymbolRepr.symbolTests
  , Test.TH.thTests
  , Test.Vector.vecTests
  ]
