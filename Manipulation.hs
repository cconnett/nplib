{-# OPTIONS -fglasgow-exts #-}

module Manipulation
    where

import Data.List
import Voting hiding (beats)
import ILPSAT
import ILPSATReduction
import Utilities
import Embeddings
import Test.QuickCheck
import qualified Data.Set as S
import Solvers
import Maybe
import Debug.Trace

import Foreign (unsafePerformIO)
    
type MPR a = Candidate a -> Int -> [Vote a] -> Problem (VoteDatum a)
instance (Num a, Show a, Ord a) => Read (MPR a)  where
    readsPrec _ "plurality" = [(scoringProtocolManipulation (\n -> 1:(repeat 0)), "")]
    readsPrec _ "borda" = [(scoringProtocolManipulation (\n -> [n-1,n-2..0]), "")]
    --readsPrec _ "irv" = [(irvManipulation (\n -> 1:(repeat 0)), "")]
    readsPrec _ _ = error $ "Supported rules are\nplurality\nborda\nirv\n"

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

prop_FindFastFinitePresent target list = any (>target) list ==>
    ((fromJust $ findFast (>target) (sort list)) ==
     (head $ dropWhile (<=target) (sort list)))

prop_FindFastFiniteAbsent target list =
    all (<=target) list ==> ((findFast (>target) (sort list)) == Nothing)

prop_FindFastInfinite target starting = it == Just starting || it == Just (target + 1)
    where it = findFast (>target) [starting..]

-- Support functions for brute force crack
                       
-- nub with an upper limit
nub' :: Eq a => Int -> [a] -> [a]
nub' n list
    | length currentSet == min (length list) n = currentSet
    | otherwise = nub' n $ currentSet ++ (drop n list)
    where currentSet = nub $ take n list

prop_nub'_nub list = nub list == nub' (length list) list
prop_nub'_subset list = length list >= 3 ==> S.fromList (nub' 3 list) `S.isSubsetOf` S.fromList list

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

-- Reductions of manipulation instances for specific classes of voting
-- rules to mixed SAT and ILP problem instance.
    
data VoteDatum a = VoteDatum {vdVoter :: Int, vdCandidate :: Candidate a, vdPosition :: Int}
                 | PairwiseDatum {pwVoter :: Int, pwCandidateA, pwCandidateB :: Candidate a}
                 | Eliminated {eRound :: Int, eCandidate :: Candidate a}
    deriving (Show, Read, Eq, Ord)
isVoteDatum (VoteDatum _ _ _) = True
isVoteDatum _ = False
isElimination (Eliminated _ _) = True
isElimination _ = False
             
scoringProtocolManipulation :: (Eq a, Integral k, Show a) =>
                               (k -> [k]) -> Candidate a -> Int -> [Vote a] ->
                               Problem (VoteDatum a)
scoringProtocolManipulation s target manipulators votes = 
    let voterSet = [0..length votes - 1]
        manipulatorSet = [length votes .. length votes + manipulators - 1]
        candidates = extractCandidates votes
        positions = [0..length candidates - 1]
        scoreList = s (fromIntegral $ length candidates)
    in
    -- non-manipulators votes
    conjoin ([Formula $ Clause [Merely $ VoteDatum voter candidate correctPosition] :
                        [Clause [Not $ Merely $ VoteDatum voter candidate position]
                             | position <- positions, position /= correctPosition]
              | (voter, vote) <- zip voterSet votes,
                (candidate, correctPosition) <- zip (fromVote vote) positions]) :
    -- Manipulator vote constraints (no two candidates in same position).
    Formula
    [Clause [Not $ Merely (VoteDatum manipulator a position), Not $ Merely (VoteDatum manipulator b position)]
         | manipulator <- manipulatorSet,
           a <- candidates, b <- candidates, a /= b,
           position <- positions] :
    -- Manipulator vote constraints (every candidate in some position).
    Formula
    [Clause [Merely (VoteDatum manipulator c position) | position <- positions]
         | manipulator <- manipulatorSet, c <- candidates] :

    -- NB: constraint holding that no candidate is in more than one
    -- position is implied by the previous two constraints

    -- Target wins. Since the reduction from ILP to SAT assumes the
    -- inequality is <=, points are bad: points for opponents are
    -- positive, and points for our target are negative.  The target
    -- wins if the total is <= -1.
    [Inequality ([( fromIntegral (scoreList!!position), Merely $ VoteDatum voter enemy position)
                      | voter <- voterSet ++ manipulatorSet,
                        position <- positions] ++
                 [(-fromIntegral (scoreList!!position), Merely $ VoteDatum voter target position)
                      | voter <- voterSet ++ manipulatorSet,
                        position <- positions],
                 -1)
     | enemy <- delete target candidates]

beats candidates ballots
       a b r = embedProblem (show a ++ " beats " ++ show b ++ " in round " ++ show r) $
               points candidates [b] ballots [r] $ \bPoints ->
               points candidates [a] ballots [r] $ \aPoints ->
                       (Formula [Clause [Not $ Merely $ Eliminated r b]] :
                        Formula [Clause [Not $ Merely $ Eliminated r a]] :
                        (trans (10^9 + (fromCandidate a*10^6) + (fromCandidate b*10^3) + r) $
                         --(\ineq -> unsafePerformIO (do {writeFile ("ineqDump"++show a ++ show b ++ show r) (show ineq); return ineq})) $
                         Inequality ([( 1, bPoint) | bPoint <- bPoints] ++
                                     [(-1, aPoint) | aPoint <- aPoints], -1)) ++
                       [])

points candidates as vs rs = pluralizeEmbedding [point candidates a v r | a <- as, v <- vs, r <- rs]
point candidates a v r = embedConstraint ("point " ++ show r ++ " " ++ show a ++ " " ++ show v) $
                         conjoin $
                         (Formula [Clause [Not $ Merely $ Eliminated r a]]) :
                         ([Formula [Clause [Merely $ PairwiseDatum v a b, Merely $ Eliminated r b]]
                           | b <- delete a candidates])

--allOthersEliminated :: [Candidate a] -> Int -> Candidate a -> Embedding a
allOthersEliminated candidates
                    r c = embedConstraint ("all except " ++ show c ++ " eliminated in round " ++ show r)
                          (Formula [Clause [(if a == c then Not else id) $ Merely $ Eliminated r a] | a <- candidates])
                         
victories candidates ballots
          r c = (pluralizeEmbedding [beats candidates ballots c a r | a <- delete c candidates])

--shouldBeEliminated :: Proposition (VoteDatum Int) -> [Proposition (VoteDatum Int)] -> Int -> Candidate Int -> Embedding (VoteDatum Int)
shouldBeEliminated allOthersEliminated victories
                   r c = (embedConstraint (show c ++ " should be eliminated for round " ++ show (r+1))
                         (Formula $ Clause [neg allOthersEliminated] :
                          [Clause [neg victory] | victory <- victories]) ) -- :: Embedding (VoteDatum a)

--fullShouldBeEliminated :: [Candidate a] -> [Int] -> Int -> Candidate a -> Embedding (VoteDatum a)
fullShouldBeEliminated candidates ballots
                       r c lambda = allOthersEliminated candidates r c $ \aoe ->
                                    victories candidates ballots r c $ \vics ->
                                    shouldBeEliminated aoe vics r c lambda

irvManipulation s target manipulators votes = 
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..manipulators]
        ballots = voterSet ++ manipulatorSet
        candidates = extractCandidates votes
        positions = [0..length candidates - 1]
        scoreList = s (fromIntegral $ length candidates)
        beats' = beats candidates ballots
        point' = point candidates
        points' = points candidates
    in
    -- non-manipulators votes
    (conjoin
     [Formula $
       Clause [Merely $ VoteDatum voter candidate correctPosition] :
       [Clause [Not $ Merely $ VoteDatum voter candidate position]
            | position <- positions, position /= correctPosition]
       | (voter, vote) <- zip voterSet votes,
         (candidate, correctPosition) <- zip (fromVote vote) positions]) :
    -- Manipulator vote constraints (no two candidates in same position).
    Formula
    [Clause [Not $ Merely (VoteDatum manipulator a position),
             Not $ Merely (VoteDatum manipulator b position)]
         | manipulator <- manipulatorSet,
           a <- candidates, b <- candidates, a < b,
           position <- positions] :
    -- Manipulator vote constraints (every candidate in some position).
    Formula [Clause [Merely (VoteDatum manipulator c position) | position <- positions]
         | manipulator <- manipulatorSet, c <- candidates] :
    -- NB: that no candidate is in more than one position is implied
    -- by the previous two constraints.

    -- Pairwise version of positional voting data
    Formula
    [Clause [Not $ Merely (VoteDatum voter candidateA position1),
             Not $ Merely (VoteDatum voter candidateB position2),
             Merely (PairwiseDatum voter candidateA candidateB)]
                 | voter <- voterSet ++ manipulatorSet,
                   candidateA <- candidates,
                   candidateB <- candidates,
                   position1 <- positions,
                   position2 <- positions,
                   candidateA /= candidateB,
                   position1 < position2] :
    -- Pairwise beat relationship is anti-symmetric and anti-reflexive
    Formula [Clause [Not $ Merely (PairwiseDatum voter candidateA candidateB),
                     Not $ Merely (PairwiseDatum voter candidateB candidateA)]
             | voter <- voterSet ++ manipulatorSet,
               candidateA <- candidates,
               candidateB <- candidates,
               candidateA <= candidateB] :
    -- Pairwise beat relationship is total
    Formula [Clause [Merely (PairwiseDatum voter candidateA candidateB),
                     Merely (PairwiseDatum voter candidateB candidateA)]
             | voter <- voterSet ++ manipulatorSet,
               candidateA <- candidates,
               candidateB <- candidates,
               candidateA < candidateB] :
    -- Everyone's in to start (all eliminations for round 0 are false)
    Formula [Clause [Not $ Merely (Eliminated 0 candidate)] | candidate <- candidates] :
    -- Cascading elimination status
    Formula [Clause [Not $ Merely (Eliminated round candidate),
                     Merely (Eliminated (round+1) candidate)]
             | round <- [1{-no one can be out in round 0-}..length candidates - 2{-|C|-1 is last round-}],
               candidate <- candidates] :

    -- Target candidate still remains after |C| - 1 rounds, with everyone else eliminated, and therefore wins
    
    Formula [Clause [(if c == target then Not else id) $ Merely $ Eliminated (length candidates - 1) c]
             | c <- candidates ] :
    {-
    Formula [Clause [Merely $ Eliminated 1 (Candidate 1)
                    ,Merely $ Eliminated 1 (Candidate 2)
                    ,Merely $ Eliminated 1 (Candidate 3)
                    ]] :
     -}
--    Formula [Clause [      Merely $ Eliminated 1 (Candidate 1)]] :
--    Formula [Clause [Not $ Merely $ Eliminated 1 (Candidate 3)]] :
--    Formula [Clause [      Merely $ Eliminated 2 (Candidate 1)]] :
--    Formula [Clause [      Merely $ Eliminated 2 (Candidate 3)]] :
    
    --tautology (beats' (Candidate 3) (Candidate 1) 0) ++
    --tautology (fullShouldBeEliminated candidates ballots 0 (Candidate 1)) ++
    --unsat     (fullShouldBeEliminated candidates ballots 0 (Candidate 2)) ++
    --unsat     (fullShouldBeEliminated candidates ballots 0 (Candidate 3)) ++
              
    --unsat     (fullShouldBeEliminated candidates ballots 0 (Candidate 1)) ++
    --unsat     (fullShouldBeEliminated candidates ballots 1 (Candidate 2)) ++
    --tautology (fullShouldBeEliminated candidates ballots 1 (Candidate 3)) ++

-- Every ballot must give a point to one candidate and only one candidate in each round.

    (concat [points' candidates [v] [r] $ \pointCsVR -> [Formula [Clause pointCsVR]]
              | v <- voterSet ++ manipulatorSet,
                r <- [0..length candidates - 2]]) ++
    (concat [point' a v r $ \pointAVR ->
             point' b v r $ \pointBVR ->
             [Formula [Clause [Not $ pointAVR, Not $ pointBVR]]]
             | v <- voterSet ++ manipulatorSet,
               r <- [0..length candidates - 2],
               a <- candidates,
               b <- candidates, a < b]) ++

    -- Elimination: this is the heart of the formula.  This works on a
    -- two-way basis.  We protect candidates who strictly beat another
    -- non-eliminated candidate, and also force out all candidates who
    -- do not meet this criterion.  Both sides are needed to deny the
    -- SAT solver any liberty in deciding who is eliminated (by means
    -- other than selecting manipulator ballots).  For every pair of
    -- distinct candidates in a given round where both are still in,
    -- if one strictly beats the other, that candidate is protected
    -- from elimination.

    concat
    [beats' a b r $ \aBeatsB ->
     [Formula [Clause [Not aBeatsB, Not $ Merely $ Eliminated (r+1) a]]]
     --[Formula [Clause [aBeatsB, neg aBeatsB]]]
     --[]
     | a <- candidates,
       b <- candidates, a /= b,
       r <- [0..length candidates - 2 {-we only perform eliminations up to the last round-}]] ++

    concat
    [allOthersEliminated candidates r c $ \aoe ->
     victories candidates ballots r c $ \vics ->
     shouldBeEliminated aoe vics r c $ \bShouldBeEliminated ->
     [equivalent bShouldBeEliminated (Merely $ Eliminated (r+1) c)]
     --[]
     | c <- candidates,
       r <- [0..length candidates - 2 {-we only perform eliminations up to the last round-}]] ++
--}
 --fullShouldBeEliminated candidates ballots r b $ \bShouldBeEliminated ->
    []

possibleWinnersBySolver :: (Show a, Ord a, Solver s) => s -> MPR a -> Int -> [Vote a] -> [Candidate a]
possibleWinnersBySolver solver manipulationProblemEr manipulators election =
    trace (show manipulators) $
    {-# scc "the filter" #-} filter (\candidate -> {-# scc "solve a cand" #-} solve solver $ {-# scc "make the problem" #-} manipulationProblemEr candidate manipulators election) candidates
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
