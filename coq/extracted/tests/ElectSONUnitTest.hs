{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Data.Text
import Data.Set (Set)
import qualified Data.Set as Set
import System.Random
import System.IO

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML
import Test.Tasty.QuickCheck

import qualified Data.ByteString.Lazy as B
import Text.Parsing.ElectSON

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

main :: IO ()
main = tests >>= defaultMainWithIngredients ingrs

ingrs :: [Ingredient]
ingrs =
   [ antXMLRunner
   ]
   ++
   defaultIngredients

tests :: IO TestTree
tests = localOption (QuickCheckTests 10000) . testGroup "ElectSON Tests" <$> sequence
  [ test_deserialize_succeeds
  ]


test_deserialize_succeeds :: IO TestTree
test_deserialize_succeeds = do
  h <- openFile "test-data/electson_trivial_stringcandidates.json" ReadMode
  f <- B.hGetContents h
  return $ testCase "ElectSON Deserialize"
         $ checkElection (getElection f)
           (Set.fromList ["Alice", "Betty"])
           [ Ballot ["Alice", "Betty"]
           , Ballot ["Alice"]
           , Ballot ["Betty", "Alice"]
           ]

checkElection :: Either String (Election Text)
              -> Set Text
              -> [Ballot Text]
              -> Assertion
checkElection (Left msg) _ _ = assertFailure (show msg)
checkElection (Right elec) cs bs = do
  assertEqual "candidates" (electionCandidates elec) cs
  assertEqual "ballots"    (electionBallots elec)    bs
