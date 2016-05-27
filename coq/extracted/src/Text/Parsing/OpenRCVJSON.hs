{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Text.Parsing.OpenRCVJSON
( Candidates(..)
, TestCase(..)
, getCandidates
, getTestCase
, testElection
, TestResult(..)
, testElectionOutput
) where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import qualified Data.List as L
import Data.Foldable
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as BC
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.HashMap.Strict as H
import Data.Vector (Vector)
import qualified Data.Vector as Vec
import Data.Scientific (toBoundedInteger)
import Data.Text (Text)
import qualified Data.Text as T

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Parser

import Text.Parsing.ElectSON (Ballot(..), Election(..), ElectionResults(..), getElectionResults)

import qualified Text.Parsec as P
import qualified Text.Parsec.Text as P

data Candidates =
  Candidates
    { csNames :: [Text]
    }
  deriving (Show)

getCandidates :: ByteString -> Either String Candidates
getCandidates input = case eitherDecode input of
  Left e -> Left ("Input was not valid JSON Value: " ++ e)
  Right v -> parseEither parseCandidates v

parseCandidates :: Value -> Parser Candidates
parseCandidates = withObject "toplevel" $ \e -> do
  cnames <- e .: "candidate_names"
  case L.nub cnames == cnames of
    True -> return (Candidates cnames)
    False -> fail "duplicate candidate names"

data TestCase =
  TestCase
    { tcMeta   :: Object
    , tcInput  :: ElectionInput
    , tcOutput :: ElectionOutput
    } deriving (Show)

data ElectionInput =
  ElectionInput
    { eiNumCandidates :: Integer
    , eiBallots       :: [Ballot Integer]
    } deriving (Show)

getTestCase :: Int -> ByteString -> Either String TestCase
getTestCase index input = case eitherDecode input of
  Left e -> Left ("Input was not valid JSON Value: " ++ e)
  Right v -> parseEither (parseTestCase index) v

parseTestCase :: Int -> Value -> Parser TestCase
parseTestCase idx = withObject "toplevel" $ \e -> do
  tcs <- e .: "test_cases"
  withArray "test_cases" parseArray tcs
  where
  parseArray vec = do
    mtc <- foldlM aux Nothing vec
    case mtc of
      Just tc -> return tc
      Nothing -> fail e

  aux (Just a) = const $ return (Just a)
  aux _ = withObject "test case" $ \obj -> do
    i <- obj .: "input"
    m <- i   .: "_meta"
    x <- m   .: "index"
    if x /= idx then return Nothing
    else do
      -- We only want to try parsing the input/output objects for the particular
      -- test we're looking for. Other tests may be malformed and we don't want
      -- those to cause an error.
      o'<- obj .: "output"
      e <- parseElectionInput i
      o <- parseElectionOutput o'
      let tc = TestCase
            { tcMeta = m
            , tcInput = e
            , tcOutput = o
            }
      return $ Just tc

  e = "Test case with index " ++ (show idx)
    ++ " could not be found"

parseElectionInput :: Object -> Parser ElectionInput
parseElectionInput o = do
  n <- o .: "candidate_count"
  b <- o .: "ballots"
  bs <- parseBallots b n
  return ElectionInput
    { eiNumCandidates = n
    , eiBallots = bs
    }

-- this function is partial but i'm being lazy about catching the errors right
-- now. inviariants are guaranteed by the parser (but of course i never
-- documented what those invariants are)
-- should replace it with one that catches errors
testElection :: Candidates -> TestCase -> Either String (Election Text)
testElection Candidates{..} TestCase{..} = Right Election{..}
  where
  ElectionInput{..}  = tcInput
  electionMeta       = tcMeta
  numCandidates      = fromInteger eiNumCandidates
  candidates         = take numCandidates csNames -- invariant - list contains no dupes, num candidates in bound
  electionCandidates = Set.fromList candidates
  electionBallots    = fmap lookupBallot eiBallots
  lookupBallot (Ballot vs) = Ballot (lookupCandidate <$> vs)
  lookupCandidate v  = candidates L.!! (fromInteger (v - 1)) -- invariant: less than int_max candidates, all ballots refer to existing candidates

ballotText :: Ballot Integer -> Text
ballotText (Ballot vs) = T.intercalate (T.pack " ")
  [ T.pack (show v) | v <- vs ]

data TestResult
  = TestResultMatch
  | TestResultMismatch String

testElectionOutput :: Candidates -> TestCase -> ElectionResults Text -> TestResult
testElectionOutput _cs _tc _er = TestResultMismatch "testElectionOutput is unimplemented!!"

data ElectionOutput =
  ElectionOutput
    { erRounds :: [ElectionRound]
    } deriving (Eq, Show)

data ElectionRound =
  ElectionRound
    { erElected :: Set Text
    , erTotals  :: Map Text Int
    } deriving (Eq,Show)

parseElectionOutput :: Object -> Parser ElectionOutput
parseElectionOutput o = do
    rs <- o .: "rounds"
    erRounds <- mapM parseRound rs
    return ElectionOutput{..}

parseRound :: Value -> Parser ElectionRound
parseRound v = withObject "round" aux v
  where
  aux o = do
    e <- o .: "elected"
    erElected <- parseElected e
    t <- o .: "totals"
    erTotals  <- parseTotals t
    return ElectionRound{..}


parseElected :: Array -> Parser (Set Text)
parseElected a = do
  -- Let it be known: this is the first time I have ever written Haskell that
  -- would benefit from the Foldable/Traversable proposal
  es <- mapM (withText "elected" return) (Vec.toList a)
  return (Set.fromList es)

parseTotals :: Object -> Parser (Map Text Int)
parseTotals o = do
  vs <- mapM parseTotal (H.toList o)
  return (Map.fromList vs)
  where
  parseTotal (k,v) = do
    votes <- withScientific "vote count" (parseInt k) v
    return (k, votes)
  parseInt k s = case toBoundedInteger s of
    Just i -> return i
    Nothing -> fail ("Vote count of " ++ show s ++ " for "
                  ++ T.unpack k ++ " is not an integer.")

parseBallots :: Array -> Integer -> Parser [Ballot Integer]
parseBallots a numCandidates = L.concat <$> mapM aux (Vec.toList a)
  where
  aux :: Value -> Parser [Ballot Integer]
  aux (String b) = case ballotFromText numCandidates b of
    Left e -> fail (show e)
    Right (n, b) -> return (take (fromInteger n) (repeat b))
  aux v = typeMismatch "string ballot representation" v


ballotFromText :: Integer -> Text -> Either P.ParseError (Integer, Ballot Integer)
ballotFromText numCandidates = P.parse parseBallot ""
  where
  parseBallot :: P.Parser (Integer, Ballot Integer)
  parseBallot = do
    -- A ballot string is an integer followed by many integers. The first
    -- integer indicates how many times an identical ballot was cast in an
    -- election. The remaining integers indicate the candidates voted for, in
    -- rank order, by the ballot.
    ns <- P.sepBy decimal (P.char ' ')
    case ns of
      n:vs | n > 0 -> return (n, Ballot vs)
      [] -> fail "ballot text must be at least one integer"

  decimalCandidate :: P.Parser Integer
  decimalCandidate = do
    c <- decimal
    case c > 0 && c <= numCandidates of
      True -> return c
      False -> fail ("candidate out of range: " ++ show c)

  decimal :: P.Parser Integer
  decimal = decDigit >>= go
   where
    decDigit = digitValue <$> P.digit

    digitValue :: Char -> Integer
    digitValue c = fromIntegral (fromEnum c - fromEnum '0')

    go i = P.try (do d <- decDigit
                     go (10*i + d))
           P.<|> return i
