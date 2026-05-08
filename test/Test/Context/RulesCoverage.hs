{-# LANGUAGE OverloadedStrings #-}

-- | Meta-tests: asserts that every RULE defined in Context/Unsafe.hs has
-- a corresponding semantic correctness test and an inspection test.

module Test.Context.RulesCoverage (tests) where

import           Data.List (isInfixOf, sort, (\\))
import qualified Test.Tasty as TT
import qualified Test.Tasty.HUnit as TTH

sourceFile :: FilePath
sourceFile = "src/Data/Parameterized/Context/Unsafe.hs"

semanticsFile :: FilePath
semanticsFile = "test/Test/Context/RulesSemantics.hs"

inspectionFile :: FilePath
inspectionFile = "test/Test/Context/Rules.hs"

extractRuleNames :: String -> [String]
extractRuleNames = concatMap extract . lines
  where
    extract l
      | "{-# RULES \"" `isInfixOf` l = firstQuoted (snd (break (== '"') l))
      | otherwise = []
    firstQuoted ('"':rest) = [takeWhile (/= '"') rest]
    firstQuoted _ = []

extractTestNames :: String -> [String]
extractTestNames = concatMap extract . lines
  where
    extract l
      | "testPropertyNamed" `isInfixOf` l = firstQuoted (dropWhile (/= '"') l)
      | "testCase" `isInfixOf` l = firstQuoted (dropWhile (/= '"') l)
      | otherwise = []
    firstQuoted ('"':rest) = [takeWhile (/= '"') rest]
    firstQuoted _ = []

-- Extract rule names referenced in inspection test section comments
-- (lines like "-- Fusion rules: fmapFC/fmapFC" or
-- "-- Identity: fmapFC/id").
extractInspectedRules :: String -> [String]
extractInspectedRules = concatMap extract . lines
  where
    extract l
      | "-- " `isInfixOf` l && any (`isInfixOf` l) prefixes =
          case dropWhile (/= ':') l of
            (':':' ':rest) -> [takeWhile (\c -> c /= ' ' && c /= '\n') rest]
            _ -> []
      | otherwise = []
    prefixes = ["Fusion rules:", "Specialization:", "Cancellation:", "Identity:"]

tests :: TT.TestTree
tests = TT.testGroup "Assignment RULES (coverage)"
  [ TTH.testCase "every RULE has a semantic test" $ do
      src <- readFile sourceFile
      sem <- readFile semanticsFile
      let ruleNames = sort (extractRuleNames src)
          testNames = sort (extractTestNames sem)
          missing = ruleNames \\ testNames
      TTH.assertBool
        ("Rules without semantic tests: " ++ show missing)
        (null missing)
  , TTH.testCase "every RULE has an inspection test" $ do
      src <- readFile sourceFile
      insp <- readFile inspectionFile
      let ruleNames = sort (extractRuleNames src)
          inspected = sort (extractInspectedRules insp)
          missing = ruleNames \\ inspected
      TTH.assertBool
        ("Rules without inspection test: " ++ show missing)
        (null missing)
  ]
