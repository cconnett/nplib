{-# OPTIONS -fglasgow-exts #-}

module Manipulation
    where

import Control.Exception
import Control.Concurrent.MVar
import Data.Array.IArray
import Data.List
import Embeddings
import Foreign (unsafePerformIO)
import Maybe
import NPLib
import Prelude hiding (catch)
import Reductions
import SatSolvers
import Test.QuickCheck
import Utilities
import Voting hiding (beats)
import qualified Data.Map as M
import qualified Data.Set as S

import Tracing

-- Conitzer and Sandholm's Find-Two-Winners [CS03]
findTwoWinners :: (Eq a) => Rule a -> Int -> [Vote a] -> ([Candidate a], [Candidate a])
findTwoWinners rule manips votes = (filter canWin candidates, [])
    where candidates = extractCandidates votes
          canWin candidate = [candidate] == (rule candidates $
                             votes ++ (replicate manips $
                                       (Vote ([candidate] ++ pack ++ [leader]))))
              where pack = delete candidate $ delete leader $ candidates
                    leader = head $ rule candidates votes -- arbitrary leader if tie exists

-- Brute force crack of possible winners
possibleWinnersByBruteForce :: Eq a => Rule a -> Int -> [Vote a] -> ([Candidate a], [Candidate a])
possibleWinnersByBruteForce rule manipulators votes
    | manipulators > length votes = (candidates, [])
    -- more manips than candidates: all candidates can be made to win!
    -- (in reasonable voting systems, assumed)
    | otherwise = myTrace 2 ("brute forcing: " ++ show manipulators) $
                  (nub' (length candidates) $ concat $
                   map (uniqueWinner . (rule candidates) . (++votes) . (manipulatorVotes candidates)) $
                   manipulatorVoteRankWeights manipulators (factorial $ length candidates),
                   [])
    where candidates = extractCandidates votes

uniqueWinner [winner] = [winner]
uniqueWinner group = []

-- Support functions for brute force crack

manipulatorVoteRankWeights :: Int -> Int -> [[Int]]
manipulatorVoteRankWeights 0 slots = [replicate slots 0]
manipulatorVoteRankWeights points 1 = [[points]]
manipulatorVoteRankWeights points slots = concat [map (c:) (manipulatorVoteRankWeights (points-c) (slots-1)) | c <- [0..points]]

manipulatorVotes :: (Eq a) => [Candidate a] -> [Int] -> [Vote a]
manipulatorVotes candidates rankWeights = concat $ [replicate i (Vote vote) | (i, vote) <- zip rankWeights $ map (unrank candidates) [0..(factorial $ length candidates)]]

unrank :: (Eq a) => [a] -> Int -> [a]
unrank [x] _ = [x]
unrank objects rank = x : unrank (delete x objects) (rank `mod` b)
    where x = objects !! (rank `div` b)
          b = factorial $ length objects - 1

factorial n = product [2..n]

--myTrace 2 ("sat solving: " ++ show manipulators) $
possibleWinnersBySolver :: SatSolver -> ManipulationProblem -> Int -> [Vote Int] ->
                          ([Candidate Int], [Candidate Int])
possibleWinnersBySolver solver manipulationProblem manipulators votes =
    let numVotes = length votes
        candidates = extractCandidates votes
        candRange = (minimum candidates, maximum candidates)
        statefulCache = unsafePerformIO $ newMVar (M.empty)
        candidateSolver votes manipulators target =
            unsafePerformIO $ do
              cache <- takeMVar statefulCache
              let ans = case cache of
                          _ | any (\k -> M.findWithDefault False (votes, k, target) cache)
                                   [manipulators, manipulators - 1 .. 0] -> Just True
                          _ | not $ all (\k -> M.findWithDefault True (votes, k, target) cache)
                                   [manipulators .. numVotes + 1] -> Just False
                          otherwise -> execNProgram solver (manipulationProblem votes manipulators target)
              putMVar statefulCache (case ans of
                                       Nothing -> cache
                                       Just bool -> M.insert (votes, manipulators, target) bool cache)
              return ans
    in
      if manipulators > numVotes then (candidates, []) else
          filter3 (candidateSolver votes manipulators) candidates

minimumManipulators :: ((Int -> Bool) -> [Int] -> Maybe Int) ->
                       (Int -> [Vote Int] -> ([Candidate a], [Candidate a])) ->
                       [Vote Int] -> ([Int], [Int])
minimumManipulators searchFunction possibleWinners election =
    (take (length candidates) $ minToWinLower 1 0,
     take (length candidates) $ minToWinUpper 1 0)
    where candidates = extractCandidates election
          possibleWinnersCache = map ((flip possibleWinners) election) [0..]
          minToWinLower n prevCutoff = value : (minToWinLower (n+1) value)
              where value = fromJust $ searchFunction pred [prevCutoff..]
                    pred m = n <= (length $ concat $ [fst $ possibleWinnersCache !! m,
                                                      snd $ possibleWinnersCache !! m])
          minToWinUpper n prevCutoff = value : (minToWinUpper (n+1) value)
              where value = fromJust $ searchFunction pred [prevCutoff..]
                    pred m = n <= (length $ fst $ possibleWinnersCache !! m)
