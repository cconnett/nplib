module Reductions where

import Voting hiding (beats)
import ILPSAT
import ReductionComponents
import Hash

import Data.List

import Utilities

type MPR a = Int -> [Vote a] -> (Problem (VoteDatum a), [Vote a] -> Candidate a -> Problem (VoteDatum a))
instance (Num a, Show a, Ord a, Hash a) => Read (MPR a)  where
    readsPrec _ "plurality" = [(scoringProtocolManipulation (\n -> 1:(repeat 0)), "")]
    readsPrec _ "borda" = [(scoringProtocolManipulation (\n -> [n-1,n-2..0]), "")]
    readsPrec _ "veto" = [(scoringProtocolManipulation (\n -> replicate (n-1) 1 ++ [0]), "")]
    readsPrec _ "irv" = [(irvManipulation, "")]
    readsPrec _ _ = error $ "Supported rules are\nplurality\nborda\nveto\nirv\n"
                    
scoringProtocolManipulation :: (Eq a, Integral k, Show a) =>
                               (k -> [k]) -> Int -> [Vote a] ->
                               (Problem (VoteDatum a), [Vote a] -> Candidate a -> Problem (VoteDatum a))
scoringProtocolManipulation s manipulators votes =
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..manipulators]
        candidates = extractCandidates votes
        positions = [0..length candidates-1]
        scoreList = s (fromIntegral $ length candidates)
    in (concat [manipulatorPositionalPositionInjection manipulatorSet candidates positions,
                manipulatorPositionalPositionSurjection manipulatorSet candidates positions]
       , \votes target ->
        nonManipulatorPositionalVotes votes voterSet candidates positions ++
        -- Target wins. Since the reduction from ILP to SAT assumes
        -- the inequality is <=, points are bad: points for opponents
        -- are positive, and points for our target are negative.  The
        -- target wins if the total is <= -1.
        [Inequality ([( fromIntegral (scoreList!!position), Merely $ VoteDatum voter opponent position)
                          | voter <- voterSet ++ manipulatorSet,
                            position <- positions] ++
                     [(-fromIntegral (scoreList!!position), Merely $ VoteDatum voter target position)
                          | voter <- voterSet ++ manipulatorSet,
                            position <- positions],
                 -1)
         | opponent <- delete target candidates])

irvManipulation manipulators votes =
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..manipulators]
        ballots = voterSet ++ manipulatorSet
        candidates = extractCandidates votes
        positions = [0..length candidates - 1] in
    let beats' = beats candidates ballots
        point' = point candidates
        points' = points candidates
    in (concat [--nonManipulatorPositionalVotes,
                --manipulatorPositionalPositionSurjection,
                --manipulatorPositionalPositionInjection,
                manipulatorPairwiseBeatsASAR manipulatorSet candidates,
                manipulatorPairwiseBeatsTotal manipulatorSet candidates] ++
        -- Everyone's in to start (all eliminations for round 0 are false)
        [Formula [Clause [Not $ Merely (Eliminated 0 candidate)] | candidate <- candidates]] ++
        -- Cascading elimination status
        [Formula [Clause [Not $ Merely (Eliminated round candidate),
                          Merely (Eliminated (round+1) candidate)]
                  | round <- [1{-no one can be out in round 0-}..length candidates - 2{-|C|-1 is last round-}],
                    candidate <- candidates]] ++
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

    -- Elimination: We protect candidates who strictly beat another
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
         | a <- candidates,
           b <- candidates, a /= b,
           r <- [0..length candidates - 2 {-we only perform eliminations up to the last round-}]] ++

        concat
        [allOthersEliminated candidates r c $ \aoe ->
         victories candidates ballots r c $ \vics ->
         shouldBeEliminated aoe vics r c $ \bShouldBeEliminated ->
             [equivalent bShouldBeEliminated (Merely $ Eliminated (r+1) c)]
         | c <- candidates,
           r <- [0..length candidates - 2 {-we only perform eliminations up to the last round-}]]

       , \votes target ->
        nonManipulatorPairwiseVotes votes voterSet candidates ++
        -- Target candidate still remains after |C| - 1 rounds, with everyone else eliminated, and therefore wins
        [Formula [Clause [(if c == target then Not else id) $ Merely $ Eliminated (length candidates - 1) c]
             | c <- candidates ]])
