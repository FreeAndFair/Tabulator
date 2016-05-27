{-# LANGUAGE CPP #-}

module Text.Parsing.BLT
( Election(..)
, Ballot(..)
, parseBallot
, parseElection
, getElection
, getElectionFromFile
) where

#if !MIN_VERSION_base(4,8,0)
import Data.Functor
#endif

import System.IO
import Text.Parsec
import Text.Parsec.String

getElectionFromFile :: FilePath -> IO (Either ParseError Election)
getElectionFromFile fp = do
  h <- openFile fp ReadMode
  getElection <$> hGetContents h

getElection :: String -> Either ParseError Election
getElection input = parse parseElection "" input

data Election =
  Election
  { electionTitle :: String
  , electionNumCandidates :: Integer
  , electionCandidates :: [String]
  , electionSeats      :: Integer
  , electionWithdrawnCandidates :: [Integer]
  , electionBallots :: [Ballot]
  }
 deriving (Show)

data Ballot =
  Ballot
  { ballotId :: String
  , ballotWeight :: Integer
  , ballotRanks :: [[Integer]]
  }
 deriving (Show)

parseElection :: Parser Election
parseElection = do
  numCand <- decimal
  spaces
  numSeat <- decimal
  manyTill space (try endOfLine)
  withdrawn <- parseWithdrawn
  ballots <- manyTill parseBallot (char '0' >> endOfLine)
  candidates <- sequence [ do nm <- parseString; endOfLine; return nm
                         | _i <- [ 1 .. numCand ]
                         ]
  title <- parseString
  spaces
  eof
  return (Election title numCand candidates numSeat withdrawn ballots)

-- TODO... what is actually the lexical structure of these strings?
parseString :: Parser String
parseString = between (char '\"') (char '\"') (many (noneOf "\""))

parseWithdrawn :: Parser [Integer]
parseWithdrawn =
  (sepBy1 (char '-' >> decimal) spaces)
  <|>
  return []

parseBallot :: Parser Ballot
parseBallot = do
  id <- try (do id <- parseId
                spaces
                return id)
        <|>
        return ""
  spaces
  w <- decimal
  spaces
  rs <- parseRanks
  manyTill space (try endOfLine)
  return (Ballot id w rs)


parseId :: Parser String
parseId = between (char '(') (char ')') (many (noneOf "()\n"))

parseRanks :: Parser [[Integer]]
parseRanks =
  (try (char '0') >> return [])
  <|>
  ( do r <- parseRank
       spaces
       rs <- parseRanks
       return (r:rs)
  )

parseRank :: Parser [Integer]
parseRank =
   (char '-' >> return [])
   <|>
   (sepBy1 decimal (char '='))

decimal :: Parser Integer
decimal = decDigit >>= go
 where
  decDigit = digitValue <$> digit

  digitValue :: Char -> Integer
  digitValue c = fromIntegral (fromEnum c - fromEnum '0')

  go i = try (do d <- decDigit
                 go (10*i + d))
         <|> return i
