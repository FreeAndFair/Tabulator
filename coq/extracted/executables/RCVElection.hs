{-# LANGUAGE RecordWildCards #-}

module Main where

import System.IO
import System.Exit
import qualified Data.ByteString.Lazy as B
import Data.Set (Set)
import qualified Data.Set as Set
import Text.Parsing.ElectSON

import BinIntConvert
import SF_imp

main :: IO ()
main = do
  input <- B.hGetContents stdin
  election <- catchParseErr "election" (getElection input)
  let results = run election
  B.hPut stdout (encodeResults results)
  return ()

catchParseErr :: (Show a) => String -> Either String a -> IO a
catchParseErr _ (Right a) = return a
catchParseErr ctx (Left e) = hPutStrLn stderr msg >> exitFailure
  where msg = "Fatal: when parsing " ++ ctx ++ ": " ++ e


run :: Eq c => Election c -> ElectionResults c
run Election{..} = ElectionResults{..}
  where
  electionResultsMeta = electionMeta
  electionBins = fmap (fmap (fmap n2int)) electionBins0
  ((electionWinner, electionRecord), electionBins0) = run_election
    relDec
    tieBreak
    (map coqBallot electionBallots)
    (coqCandidates electionCandidates)

relDec :: Eq c => c -> c -> Bool
relDec = (==)

-- Picked arbitrarily
tieBreak :: [c] -> Maybe c
tieBreak [] = Nothing
tieBreak (c:_) = Just c

coqBallot :: Ballot c -> Coq_ballot c
coqBallot (Ballot vs) = map (\v -> [v]) vs

coqCandidates :: Set c -> [c]
coqCandidates = Set.toList
