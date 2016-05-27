{-# LANGUAGE CPP #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE StandaloneDeriving #-}
module Main (main) where

import Data.List
import System.Random

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients
import Test.Tasty.Runners.AntXML
import Test.Tasty.QuickCheck

import Text.Parsec.Error

import SF_tests
import qualified SF_imp
import qualified BinNums

import Text.Parsing.BLT
import BinIntConvert

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
tests = localOption (QuickCheckTests 10000) . testGroup "SF Tests" <$> sequence
  [ return $ testProperty "drop_none_keeps" prop_drop_none_keeps
  , return $ testProperty "next_ranking_contains" prop_next_ranking_contains
  , return $ testProperty "next_ranking_not_eliminated" prop_next_ranking_not_eliminated
  , return $ testProperty "next_ranking_not_overvote" prop_next_ranking_not_overvote
  , return $ testProperty "increment_get" prop_increment_get
  , return $ testProperty "count_tabulate''" prop_count_tabulate''
  , return $ testProperty "option_split" prop_option_split
  , return $ testProperty "get_bottom_votes_correct" prop_get_bottom_votes_correct
  , test_SF2012_D5
  , test_SF2011_Sheriff
  , test_SF2011_Mayor
  ]


-- Test that our implementation chooses the expected winner for historical
-- elections in San Fransisco.

test_SF2012_D5 :: IO TestTree
test_SF2012_D5 = do
  elec <- getElectionFromFile "test-data/SanFrancisco-2012-D5.blt"
  return $ testCase "SF2012_D5" (checkElec elec "LONDON BREED")

test_SF2011_Sheriff :: IO TestTree
test_SF2011_Sheriff = do
  elec <- getElectionFromFile "test-data/SanFrancisco-2011-Sheriff.blt"
  return $ testCase "SF2011_Sheriff" (checkElec elec "ROSS MIRKARIMI")

test_SF2011_Mayor :: IO TestTree
test_SF2011_Mayor = do
  elec <- getElectionFromFile "test-data/SanFrancisco-2011-Mayor.blt"
  return $ testCase "SF2011_Mayor" (checkElec elec "ED LEE")


data IntTrie = IntTrie Int [IntTrie]

randomTrie :: RandomGen g => g -> IntTrie
randomTrie g0 =
  let (i, g0') = next g0
   in IntTrie i (unfoldr f g0')

 where f gen =
        let (gen1, gen2) = split gen
         in Just ( randomTrie gen1, gen2 )

lookupTrie :: [Integer] -> IntTrie -> Int
lookupTrie [] (IntTrie i _) = i
lookupTrie (x:xs) (IntTrie _ rs) = lookupTrie xs (rs !! fromIntegral x)


checkElec :: Either ParseError Election -> String -> Assertion
checkElec (Left msg) _ = assertFailure (show msg)
checkElec (Right elec) winner = do
   let bs = map ballotRanks $ electionBallots elec

   -- tiebreaking function based on a random trie
   trie <- randomTrie <$> newStdGen
   let tiebreak [] = Nothing
       tiebreak xs = Just $ xs !! (j `mod` length xs)
         where j = lookupTrie xs trie

   let allCandidates = [1 .. electionNumCandidates elec]

   -- NB candidate numbers are 1-indexed
   let getCand idx =
         electionCandidates elec !! fromIntegral (idx - 1)

   case SF_imp.run_election (==) tiebreak bs allCandidates of
     ( (Just winnerIdx, record), _rounds) -> do
        -- putStrLn $ unwords ["Election record: ", show record]
        assertEqual "Election winner" winner (getCand winnerIdx)
     ( (Nothing, _), _) ->
        assertFailure "No winner selected!"
