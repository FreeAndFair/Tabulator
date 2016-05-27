{-# LANGUAGE ScopedTypeVariables #-}

module BinIntConvert where

import Test.QuickCheck

import qualified BinNums

int2Pos :: Integral x => x -> BinNums.Coq_positive
int2Pos 1 = BinNums.Coq_xH
int2Pos x = if (x `mod` 2 == 1)
          then BinNums.Coq_xI (int2Pos (x `div` 2))
          else BinNums.Coq_xO (int2Pos (x `div` 2))

int2N :: Integral x => x -> BinNums.N
int2N x
  | x <= 0    = BinNums.N0
  | otherwise = BinNums.Npos (int2Pos x)

pos2int :: Integral x => BinNums.Coq_positive -> x
pos2int x = pos2int' x 1 where
  pos2int' (BinNums.Coq_xI h) c =  c + (pos2int' h c*2)
  pos2int' (BinNums.Coq_xO h) c = (pos2int' h c*2)
  pos2int' _ c = c

n2int :: Integral x => BinNums.N -> x
n2int (BinNums.N0) = 0
n2int (BinNums.Npos p) = pos2int p

instance Show BinNums.N where
  show x = show (n2int x :: Integer)

instance Arbitrary BinNums.N where
  arbitrary = do
    (arbN :: Int) <- ((suchThat (arbitrarySizedIntegral) ((<=) 0)))
    return  (int2N arbN)
