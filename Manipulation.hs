{-# OPTIONS -fglasgow-exts #-}

module Manipulation
    where

import Data.List
import Voting hiding (beats)
import ILPSAT
import ILPSATReduction
import Reductions
import Utilities
import Embeddings
import Hash
import Test.QuickCheck
import qualified Data.Set as S
import Solvers
import Maybe
import Debug.Trace

-- Conitzer and Sandholm's Find-Two-Winners [CS03]
findTwoWinners :: (Eq a) => Rule a -> Int -> [Vote a] -> [Candidate a]
findTwoWinners rule manips votes = filter canWin candidates
    where candidates = extractCandidates votes
          canWin candidate = [candidate] == (rule candidates $
                             votes ++ (replicate manips $
                                       (Vote ([candidate] ++ pack ++ [leader]))))
                             
              where pack = delete candidate $ delete leader $ candidates
                    leader = head $ rule candidates votes -- arbitrary leader if tie exists

-- Brute force crack of possible winners
possibleWinnersByBruteForce :: Eq a => Rule a -> Int -> [Vote a] -> [Candidate a]
possibleWinnersByBruteForce rule manipulators votes
    | manipulators > length votes = candidates
    -- more manips than candidates: all candidates can be made to win!
    -- (in reasonable voting systems, assumed)
    | otherwise = trace (show manipulators) $
                  nub' (length candidates) $ concat $
                  map (uniqueWinner.(rule candidates).(++votes).(manipulatorVotes candidates)) $
                  manipulatorVoteRankWeights manipulators (factorial $ length candidates)
    where candidates = extractCandidates votes

uniqueWinner [winner] = [winner]
uniqueWinner group = []

-- Support functions for brute force crack

manipulatorVoteRankWeights :: Int -> Int -> [[Int]]
manipulatorVoteRankWeights 0 slots = [replicate slots 0]
manipulatorVoteRankWeights points 1 = [[points]]
manipulatorVoteRankWeights points slots = concat [map (c:) (manipulatorVoteRankWeights (points-c) (slots-1)) | c <- [0..points]]

manipulatorVotes :: [Candidate a] -> [Int] -> [Vote a]
manipulatorVotes candidates rankWeights = concat $ [replicate i (Vote vote) | (i, vote) <- zip rankWeights $ map (unrank candidates) [0..(factorial $ length candidates)]]

unrank :: [a] -> Int -> [a]
unrank [x] _ = [x]
unrank objects rank = (take pos rest) ++ [head objects] ++ (drop pos rest)
    where pos = rank `div` b
          rest = unrank (tail objects) (rank `mod` b)
          b = (factorial $ (length objects)-1)

factorial n = product [2..n]

possibleWinnersBySolver :: (Show a, Ord a, Solver s) => s -> MPR a -> Int -> [Vote a] -> [Candidate a]
possibleWinnersBySolver solver manipulationProblemEr manipulators election =
    trace (show manipulators) $
    let (partialProblem, restOfProblem) = manipulationProblemEr manipulators election
        solveRest = startPartial solver partialProblem in
    filter (\candidate -> (fst . solveRest) (restOfProblem candidate)) candidates
    where candidates = extractCandidates election

minimumManipulators :: (Ord a) =>
                       (Int -> [Vote a] -> [Candidate a]) -> [Vote a] -> [Int]
minimumManipulators possibleWinners election =
    take (length candidates) $ minToWin 1 0
    where candidates = extractCandidates election
          minToWin n lowerBound = value : (minToWin (n+1) value)
              where value = fromJust $ findFast pred [lowerBound..]
                    pred m = n <= (length $ possibleWinnersCache !! m)
                    possibleWinnersCache = map ((flip possibleWinners) election) [0..]
