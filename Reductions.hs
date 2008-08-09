module Reductions where

import Voting hiding (beats)
import ILPSAT
import ILPSATReduction
import ReductionComponents
import Hash
import Embeddings
import Data.Ratio

import Data.List
import qualified Data.Map as M

import Utilities

type MPR a = [Vote a] -> (Problem (VoteDatum a), [Vote a] -> Int -> Candidate a -> Problem (VoteDatum a))
instance (Num a, Show a, Ord a, Hash a) => Read (MPR a)  where
    readsPrec _ "plurality" = [(scoringProtocolManipulation (\n -> 1:(repeat 0)), "")]
    readsPrec _ "pluralityWithRunoff" = [(pluralityWithRunoffManipulation, "")]
    readsPrec _ "borda" = [(scoringProtocolManipulation (\n -> [n-1,n-2..0]), "")]
    readsPrec _ "veto" = [(scoringProtocolManipulation (\n -> replicate (n-1) 1 ++ [0]), "")]
    readsPrec _ "irv" = [(irvManipulation, "")]
    readsPrec _ "copeland" = [(copelandManipulation (1%2), "")]
    readsPrec _ _ = error $ "Supported rules are\nplurality\npluralityWithRunoff\nborda\nveto\nirv\ncopeland\n"

scoringProtocolManipulation :: (Eq a, Integral k, Show a) =>
                               (k -> [k]) -> [Vote a] ->
                               (Problem (VoteDatum a), [Vote a] -> Int -> Candidate a -> Problem (VoteDatum a))
scoringProtocolManipulation s votes =
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..length votes + 1]
        ballots = voterSet ++ manipulatorSet
        candidates = extractCandidates votes
        positions = [0..length candidates-1]
        scoreList = s (fromIntegral $ length candidates) in
    (concat [manipulatorPositionalPositionInjection manipulatorSet candidates positions,
             manipulatorPositionalPositionSurjection manipulatorSet candidates positions] ++
     concat
     [outscores ballots positions scoreList winner loser $ \winnerOutscoresLoser ->
      [Formula [Clause [neg $ winnerOutscoresLoser, Merely $ Eliminated 0 loser]]]
          | winner <- candidates,
            loser  <- delete winner candidates] ++
     concat
     [pluralizeEmbedding [outscores ballots positions scoreList d c | d <- delete c candidates]
     $ \cOutscoredByOthers ->
         [Formula [Clause $ [neg $ Merely $ Eliminated 0 c] ++ cOutscoredByOthers]]
             | c <- candidates]
    , \votes manipulators target ->
        count ballots (length votes + manipulators) ++
        nonManipulatorPositionalVotes votes voterSet candidates positions ++
     -- Target candidate remains, with everyone else eliminated, and therefore wins
        [Formula [Clause [(if c == target then neg else id) $ Merely $ Eliminated 0 c]
                      | c <- candidates]]
    )

pluralityWithRunoffManipulation votes =
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..length votes + 1]
        ballots = voterSet ++ manipulatorSet
        candidates = extractCandidates votes
        rounds = [0,1,2] in
    let point' = point candidates
        points' = points candidates in
    (concat [manipulatorPairwiseBeatsASAR manipulatorSet candidates,
             manipulatorPairwiseBeatsTotal manipulatorSet candidates,
             eliminationBasics candidates rounds,
             firstPlacePoints candidates ballots rounds] ++
     -- Elimination: The candidates who advance are exactly those who
     -- have at least |C| - 2 victories
     concat
     [let cAdvancesTag = (show c ++ " advances to round 1")
          ineqNumber = fromIntegral $ hash cAdvancesTag in
      victories candidates ballots 0 c $ \cVictories ->
      embedProblem cAdvancesTag
       (trans ineqNumber $ Inequality ([(-1, propositionToProblem vic) | vic <- cVictories], -(length candidates - 2))) $ \cAdvances ->
      [equivalent cAdvances (neg $ Merely $ Eliminated 1 c)]
          | c <- candidates] ++
     -- Second stage elimination: can be tolerant of ties in
     -- elimination, because of requirement that all others be
     -- eliminated.
     concat
     [let cAdvancesTag = (show c ++ " advances to round 2") in
      losses candidates ballots 1 c $ \cLosses ->
      let ineqNumber = fromIntegral $ hash cAdvancesTag in
      embedFormula cAdvancesTag (Formula [Clause [neg loss] | loss <- cLosses]) $ \cAdvances ->
      [equivalent cAdvances (neg $ Merely $ Eliminated 2 c)]
          | c <- candidates]
    , \votes manipulators target ->
        count ballots (length votes + manipulators) ++
        nonManipulatorPairwiseVotes votes voterSet candidates ++
     -- Target candidate still remains in round 2, with everyone else eliminated, and therefore wins.
        [Formula [Clause [(if c == target then neg else id) $ Merely $ Eliminated 2 c]
                      | c <- candidates]]
    )

irvManipulation votes =
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..length votes + 1]
        ballots = voterSet ++ manipulatorSet
        candidates = extractCandidates votes
        positions = [0..length candidates - 1]
        rounds = [0..length candidates - 1] in
    let beats' = beats candidates ballots
        point' = point candidates
        points' = points candidates in
    (concat [manipulatorPairwiseBeatsASAR manipulatorSet candidates,
             manipulatorPairwiseBeatsTotal manipulatorSet candidates,
             eliminationBasics candidates rounds,
             firstPlacePoints candidates ballots rounds] ++
     -- Elimination: We protect candidates who strictly beat another
     -- non-eliminated candidate, and also force out all candidates
     -- who do not meet this criterion.  Both sides are needed to deny
     -- the SAT solver any liberty in deciding who is eliminated (by
     -- means other than selecting manipulator ballots).  For every
     -- pair of distinct candidates in a given round where both are
     -- still in, if one strictly beats the other, that candidate is
     -- protected from elimination.
     concat
     [beats' a b r $ \aBeatsB ->
          [Formula [Clause [neg aBeatsB, neg $ Merely $ Eliminated (r+1) a]]]
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

    , \votes manipulators target ->
        count ballots (length votes + manipulators) ++
        nonManipulatorPairwiseVotes votes voterSet candidates ++
     -- Target candidate still remains after |C| - 1 rounds, with everyone else eliminated, and therefore wins
        [Formula [Clause [(if c == target then neg else id) $ Merely $ Eliminated (length candidates - 1) c]
                      | c <- candidates ]]
    )

copelandManipulation tieValue votes =
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..length votes + 1]
        ballots = voterSet ++ manipulatorSet
        candidates = extractCandidates votes
        pvm = makePairwiseVictoryMap candidates ballots
        equivalenceContraints = concat $ map (snd . snd) (M.toList pvm)
    in
    (equivalenceContraints ++
     concat [manipulatorPairwiseBeatsASAR manipulatorSet candidates,
             manipulatorPairwiseBeatsTotal manipulatorSet candidates] ++
     concat
     [copelandScoreBetter tieValue pvm candidates winner loser $ \winnerOutscoresLoser ->
      [Formula [Clause [neg $ winnerOutscoresLoser, Merely $ Eliminated 0 loser]]]
          | winner <- candidates,
            loser  <- delete winner candidates] ++
     concat
     [pluralizeEmbedding [copelandScoreBetter tieValue pvm candidates d c | d <- delete c candidates]
     $ \cOutscoredByOthers ->
         [Formula [Clause $ [neg $ Merely $ Eliminated 0 c] ++ cOutscoredByOthers]]
             | c <- candidates]
    , \votes manipulators target ->
        count ballots (length votes + manipulators) ++
        nonManipulatorPairwiseVotes votes voterSet candidates ++
     -- Target candidate remains, with everyone else eliminated, and therefore wins
        [Formula [Clause [(if c == target then neg else id) $ Merely $ Eliminated 0 c]
                     | c <- candidates]]
    )
