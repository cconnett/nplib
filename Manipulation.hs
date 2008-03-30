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
import VarMapping
import Hash
import Test.QuickCheck
import qualified Data.Set as S
import Solvers
import Maybe
import SatSolvers

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
    | otherwise = myTrace (show manipulators) $
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

possibleWinnersBySolver :: (Show a, Ord a, Solver s) => s -> MPR a -> [Vote a] ->
                           (Int -> [Vote a] -> [Candidate a])
possibleWinnersBySolver solver manipulationProblemEr election =
    let numVotes = length election
        candidates = extractCandidates election
        cache = map ((\problem ->
                          let clauses = sortNub $ fromFormula $ conjoin problem
                              vm = varMap clauses in
                          (toDIMACS vm (Formula clauses), vm)) .
                     (\m -> fst $ manipulationProblemEr m election)) [0..] in
    let realSolver manipulators votes =
            myTrace (show manipulators) $
            let part2 = snd $ manipulationProblemEr manipulators election
                solveRest = startPartial solver (cache !! manipulators) in
            filter (\target -> (fst . solveRest) (part2 votes target)) candidates
    in realSolver
possibleWinnersBySolverDebug solver manipulationProblemEr election =
    let numVotes = length election
        candidates = extractCandidates election
        cache = map ((\problem ->
                          let clauses = sortNub $ fromFormula $ conjoin problem
                              vm = varMap clauses in
                          (toDIMACS vm (Formula clauses), vm)) .
                     (\m -> fst $ manipulationProblemEr m election)) [0..] in
    let realSolver manipulators votes =
            myTrace (show manipulators) $
            let part2 = snd $ manipulationProblemEr manipulators election
                solveRest = startPartial solver (cache !! manipulators)
            in (\target -> solveRest (part2 votes target))
    in realSolver
minimumManipulators :: (Ord a) =>
                       (Int -> [Vote a] -> [Candidate a]) -> [Vote a] -> [Int]
minimumManipulators possibleWinners election =
    take (length candidates) $ minToWin 1 0
    where candidates = extractCandidates election
          minToWin n lowerBound = value : (minToWin (n+1) value)
              where value = fromJust $ findFast pred [lowerBound..]
                    pred m = n <= (length $ possibleWinnersCache !! m)
                    possibleWinnersCache = map ((flip possibleWinners) election) [0..]
