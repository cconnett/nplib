{-# OPTIONS -fglasgow-exts #-}

module Elections
    where

import Voting
import Data.List
import Data.Graph.Inductive
import Maybe
import Test.QuickCheck
import IO
import Control.Monad
import Data.Ord
    
type VoteGenerator a = [Candidate a] -> Gen (Vote a)

instance (Eq a) => Read (VoteGenerator a) where
    readsPrec _  str = [(parse (words str), "")]
        where parse ["uniform"] = uniformVote
              parse ["condorcet", p] = condorcetVote (read p)
              parse ["spatial", d, stddev] = spatialVote (read d) (read stddev)
              parse _ = error ("Supported distributions are\n" ++
                               (unlines distributions))

distributions :: [String]
distributions = ["uniform", "condorcet p", "spatial d stddev"]

-- generates a random set of n votes over candidates using vote
-- generator genVote
election :: (Eq a) =>
            VoteGenerator a ->
            [Candidate a] -> Int -> Gen [Vote a]
election genVote candidates n = replicateM n (genVote candidates)

-- generates a vote over candidates u.a.r. from all permuations of candidates
uniformVote :: (Eq a) => [Candidate a] -> Gen (Vote a)
uniformVote [] = return $ Vote []
uniformVote candidates =
    do let m = length candidates
       topIndex <- (choose (0, m-1))
       let c = candidates !! topIndex
       rest <- uniformVote (delete c candidates)
       return $ Vote $ c:(fromVote rest)

condorcetVote :: (Eq a) => Double -> [Candidate a] -> Gen (Vote a)
condorcetVote p trueOrder = do
  edges <- sequence [frequency [(fromIntegral (round (1000*p)), elements [(u,v,())]),
                                (fromIntegral (round (1000*(1-p))), elements [(v,u,())])]
                     | u <- [1..length trueOrder], v <- [1..length trueOrder], u < v]
  let graph = insEdges edges $ insNodes nodes $ (empty :: Gr (Candidate a) ())
  if ok graph then
      return $ Vote $ map (fromJust.(lab graph)) $ topsort graph else
      condorcetVote p trueOrder
    where nodes    = zip [1..] trueOrder
          ok graph = (length $ scc graph) == noNodes graph

uniform :: Gen Double
uniform = choose (0.0, 1.0)
                     
normal :: Double -> Double -> Gen Double
normal mean stddev = do
  a <- uniform :: Gen Double
  b <- uniform :: Gen Double
  return $ stddev * (sqrt (-2*log a) * cos (2*pi*b)) + mean

-- FIXME: candidatePositions needs to be generated once for all votes!
spatialVote :: (Eq a) => Int -> Double -> [Candidate a] -> Gen (Vote a)
spatialVote issues stddev candidates = do
  voter <- sequence $ replicate issues $ normal 0 stddev
  candidatePositions <- sequence $ replicate (length candidates) $ sequence $ replicate issues $ normal 0 stddev
  let distance voter candidate = sqrt $ sum $ zipWith (-) voter (position candidate)
      position candidate       = fromJust $ lookup candidate positionMap
      positionMap              = zip candidates candidatePositions
  return $ Vote $ sortBy (comparing (distance voter)) candidates

readElections :: String -> IO [[Vote Int]]
readElections filename = do
  handle <- openFile filename ReadMode
  electionsData <- hGetContents handle
  return $ read electionsData
