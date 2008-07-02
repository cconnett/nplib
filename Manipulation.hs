{-# OPTIONS -fglasgow-exts #-}

module Manipulation
    where

import Prelude hiding (catch)
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
import qualified Data.Map as M
import Solvers
import Maybe
import SatSolvers
import Foreign (unsafePerformIO)
import GHC.Conc
import Control.Exception

import Debug.Trace

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
    | otherwise = myTrace ("brute forcing: " ++ show manipulators) $
                  (nub' (length candidates) $ concat $
                   map (uniqueWinner.(rule candidates).(++votes).(manipulatorVotes candidates)) $
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
                           (Int -> [Vote a] -> ([Candidate a], [Candidate a]))
possibleWinnersBySolver solver manipulationProblemEr prototypeElection =
    let numVotes = length prototypeElection
        candidates = extractCandidates prototypeElection
        part1 = let clauses = sortNub $ fromFormula $
                              conjoin (fst $ manipulationProblemEr prototypeElection)
                    vm = varMap clauses
                in (toDIMACS vm (Formula clauses), vm) in
    let realSolver manipulators votes =
            myTrace ("sat solving: " ++ show manipulators) $
            let part2 = snd $! manipulationProblemEr votes
                solveRest = startPartial solver part1
                statefulCache = unsafePerformIO $ newMVar (M.empty)
                candidateSolver votes manipulators target = unsafePerformIO $ do
                  cache <- takeMVar statefulCache
                  let ans = case cache of
                        _ | any (\k -> M.findWithDefault False (votes, k, target) cache)
                                [manipulators, manipulators - 1 .. 0] -> Just True
                        _ | not $ all (\k -> M.findWithDefault True (votes, k, target) cache)
                                       [manipulators .. numVotes + 1] -> Just False
                        otherwise -> (fst . solveRest) $! (part2 votes manipulators target)
                  putMVar statefulCache
                              (case ans of
                                 Nothing -> cache
                                 Just bool -> M.insert (votes, manipulators, target) bool cache)
                  return ans
            in
            if manipulators > numVotes then
                (candidates, []) else
                filter3 (candidateSolver votes manipulators) candidates
    in realSolver
possibleWinnersBySolverDebug solver manipulationProblemEr prototypeElection =
    let numVotes = length prototypeElection
        candidates = extractCandidates prototypeElection
        part1 = let clauses = sortNub $ fromFormula $
                              conjoin (fst $ manipulationProblemEr prototypeElection)
                    vm = varMap clauses
                in (toDIMACS vm (Formula clauses), vm) in
    let realSolver manipulators votes =
            myTrace (show manipulators) $
            let part2 = snd $ manipulationProblemEr prototypeElection
                solveRest = startPartial solver part1 in
            if manipulators > numVotes then (candidates, []) else
            filter3 (\target -> (fst . solveRest) (part2 votes manipulators target)) candidates
    in realSolver

hybridSolver nullVotes solver1 solver2 = internalSolver
    where internalSolver manipulators votes
              | s2ValuesOfM !! manipulators = myTrace (show manipulators ++ " sat'd") $
                                              solver2 manipulators votes
              | otherwise                   = myTrace (show manipulators ++ " bf'd") $
                                              solver1 manipulators votes
          s2ValuesOfM = map takesTooLong [0..]
          takesTooLong m =
              unsafePerformIO $ do
                result <- newEmptyMVar
                parentId <- myThreadId
                workerId <- forkIO $ do {putMVar result $! solver1 m nullVotes;
                                         throwTo parentId (ErrorCall "Finished =D")
                                        }
                catch (threadDelay $ 50 * 10^6)
                      (const $ return ())
                killThread workerId
                computedResult <- tryTakeMVar result
                return $ isNothing computedResult

minimumManipulators :: (Ord a) =>
                       (Int -> [Vote a] -> ([Candidate a], [Candidate a])) ->
                       [Vote a] -> ([Int], [Int])
minimumManipulators possibleWinners election =
    (take (length candidates) $ minToWinLower 1 0,
     take (length candidates) $ minToWinUpper 1 0)
    where candidates = extractCandidates election
          possibleWinnersCache = map ((flip possibleWinners) election) [0..]
          minToWinLower n prevCutoff = value : (minToWinLower (n+1) value)
              where value = fromJust $ findFirst pred [prevCutoff..]
                    pred m = n <= (length $ concat $ [fst $ possibleWinnersCache !! m,
                                                      snd $ possibleWinnersCache !! m])
          minToWinUpper n prevCutoff = value : (minToWinUpper (n+1) value)
              where value = fromJust $ findFirst pred [prevCutoff..]
                    pred m = n <= (length $ fst $ possibleWinnersCache !! m)
