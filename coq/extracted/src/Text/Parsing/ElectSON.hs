{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Text.Parsing.ElectSON
( Election(..)
, Ballot(..)
, getElection
, encodeElection
, ElectionResults(..)
, encodeResults
, getElectionResults
) where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import Data.ByteString.Lazy (ByteString)
import Data.Text
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as Vec

import Data.Aeson
import Data.Aeson.Types
import Data.Aeson.Parser


data Election c =
  Election
  { electionMeta          :: Object
  , electionCandidates    :: Set c
  , electionBallots       :: [Ballot c]
  } deriving (Eq, Show)

data Ballot c = Ballot [c]
 deriving (Eq, Show)

data ElectionResults c =
  ElectionResults
  { electionResultsMeta :: Object
  , electionWinner :: Maybe c
  , electionRecord :: [[c]]
  , electionBins   :: [[(c, Integer)]]
  } deriving (Eq, Show)


getElection :: ByteString -> Either String (Election Text)
getElection input = case decode input of
  Nothing -> Left "Input was not valid JSON"
  Just v ->  parseEither parseElection v

parseElection :: Value -> Parser (Election Text)
parseElection = withObject "election" $ \e -> do
  electionMeta <- e .: "_meta"
  cs           <- e .: "candidates"
  bs           <- e .: "ballots"

  electionCandidates <- withArray "candidates"
    parseCandidates cs
  electionBallots    <- withArray "ballots"
    (parseBallots electionCandidates) bs

  return Election{..}

  where
  parseCandidates :: Array -> Parser (Set Text)
  parseCandidates a = do
    cs <- mapM aux (Vec.toList a)
    return (Set.fromList cs)
    where
    aux :: Value -> Parser Text
    aux (String t) = return t
    aux v = typeMismatch "string candidate name" v

encodeElection :: Election Text -> ByteString
encodeElection Election{..} = encode $ object
  [ "_meta"      .= electionMeta
  , "candidates" .= Vec.fromList (Set.toList electionCandidates)
  , "ballots"    .= Vec.fromList (fmap ballotVal electionBallots)
  ]
  where
  ballotVal (Ballot vs) = Array (Vec.fromList (fmap String vs))

parseBallots :: Set Text -> Array -> Parser [Ballot Text]
parseBallots candidates a = do
  bs <- mapM parseBallot (Vec.toList a)
  return bs
  where
  parseBallot :: Value -> Parser (Ballot Text)
  parseBallot  = withArray "ballot" $ \a -> do
    vs <- mapM aux (Vec.toList a)
    return (Ballot vs)
  aux :: Value -> Parser Text
  aux (String t) | Set.member t candidates = return t
                 | otherwise = typeMismatch "known candidate" (String t)
  aux v = typeMismatch "valid candidate type" v


encodeResults :: ElectionResults Text -> ByteString
encodeResults ElectionResults{..} = encode $ object
  [ "_meta"  .= electionResultsMeta
  , "winner" .= case electionWinner of
      Nothing -> object [ "error" .= String "no winner" ]
      Just w  -> String w
  , "record"  .= rs
  , "bins"    .= bs
  ]
  where
  rs = arrayOf (arrayOf String) electionRecord
  bs = arrayOf (arrayOf bin)    electionBins
  bin (c, vs) = object ["candidate" .= String c
                       , "votes"    .= Number (fromInteger vs)
                       ]
  arrayOf :: (a -> Value) -> [a] -> Value
  arrayOf f v = Array (Vec.fromList (fmap f v))

getElectionResults :: ByteString -> Either String (ElectionResults Text)
getElectionResults input = case eitherDecode input of
  Left e -> Left ("Input was not valid JSON Value: " ++ e)
  Right v -> parseEither parseElectionResults v


parseElectionResults :: Value -> Parser (ElectionResults Text)
parseElectionResults = withObject "election results" $ \r -> do
  electionResultsMeta <- r .: "_meta"
  win <- r .: "winner"
  rec <- r .: "record"
  bns <- r .: "bins"
  electionWinner <- parseWinner win
  electionRecord <- parseRecord rec
  electionBins   <- parseBins   bns
  return ElectionResults{..}
  where
  parseWinner :: Value -> Parser (Maybe Text)
  parseWinner (String s) = return (Just s)
  parseWinner (Object o) = return Nothing -- not exactly right
  parseWinner v = typeMismatch "winning candidate" v

  parseArray :: Array -> (Value -> Parser a) -> Parser [a]
  parseArray arr p = mapM p (Vec.toList arr)

  parseText :: Value -> Parser Text
  parseText (String t) = return t
  parseText v = typeMismatch "text" v

  parseRecord :: Array -> Parser [[Text]]
  parseRecord a = parseArray a $ withArray "record" $ \i -> parseArray i parseText

  parseBins :: Array -> Parser [[(Text, Integer)]]
  parseBins a = parseArray a $ withArray "bin" $ \i -> parseArray i parseBin

  parseBin :: Value -> Parser (Text, Integer)
  parseBin = withObject "bin" $ \b -> do
    c <- b .: "candidate"
    v <- b .: "votes"
    return (c,v)
