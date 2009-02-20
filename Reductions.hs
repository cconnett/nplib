module Reductions where

import Control.Monad.State
import Data.Array
import Data.Ix
import Data.List
import Data.Ratio
import Embeddings
import NInteger
import NPLib
import ReductionComponents
import SAT
import Voting hiding (beats)
import qualified Data.Map as M
import Tracing

type ManipulationProblem = [Vote Int] -> Int -> Candidate Int -> NProgramComputation ()
instance Read (ManipulationProblem)  where
    readsPrec _ "plurality" = [(scoringProtocolManipulation (\n -> 1:(repeat 0)), "")]
    readsPrec _ "pluralityWithRunoff" = [(pluralityWithRunoffManipulation, "")]
    readsPrec _ "borda" = [(scoringProtocolManipulation (\n -> [n-1,n-2..0]), "")]
    readsPrec _ "veto" = [(scoringProtocolManipulation (\n -> replicate (n-1) 1 ++ [0]), "")]
--    readsPrec _ "irv" = [(irvManipulation, "")]
--    readsPrec _ "copeland" = [(copelandManipulation (1%2), "")]
    readsPrec _ _ = error $ "Supported rules are\nplurality\npluralityWithRunoff\nborda\nveto\nirv\ncopeland\n"

scoringProtocolManipulation :: (Int -> [Int]) -> ManipulationProblem
scoringProtocolManipulation scoreFunc votes numManipulators target =
    let numNonmanipulators = length votes
        numCandidates = length $ extractCandidates votes
        candRange = (Candidate 1, Candidate numCandidates)
        posRange = (Position 1, Position numCandidates)
        voters = [0 .. numNonmanipulators + numManipulators - 1]
        scoreList = scoreFunc numCandidates in
    do
      ballots <- makePositionalBallots votes candRange posRange numManipulators
      --ntrace "Ballots" ballots (concatMap showPositionalBallot)
      candidateScores <- mapM (getScore ballots voters posRange scoreList) (range candRange)
      --ntrace "Candidate scores" candidateScores (show::[Integer]->String)
      sequence_ [(candidateScores !! index candRange loser) `lt` (candidateScores !! index candRange target) >>= assert
                 | loser  <- delete target (range candRange)]

pluralityWithRunoffManipulation :: ManipulationProblem
pluralityWithRunoffManipulation votes numManipulators target =
    let numNonmanipulators = length votes
        candidates = sort $ extractCandidates votes
        candRange = (head candidates, last candidates)
        numCandidates = length candidates
        rounds = [0,1,2] in
    do
      ballots <- makePairwiseBallots votes candRange numManipulators
      eliminations <- makeEliminations rounds candidates
      firstPlaceScores <- getFirstPlaceScores ballots candRange eliminations rounds

      ntrace "FirstPlaceScores" firstPlaceScores (show::Array (Round, Candidate Int) Integer -> String)
      ntrace "EliminationData" eliminations $ myTrace 0 (show numManipulators ++ " manipulators for " ++ show target) showEliminationData
      manipulatorPairwiseBeatsASAR (drop numNonmanipulators ballots) candidates
      manipulatorPairwiseBeatsTotal (drop numNonmanipulators ballots) candidates


      -- First round elimination: The candidates who advance are
      -- exactly those who have at least |C| - 2 victories
      forM_ candidates $ \c -> do
        victories <- victories candidates firstPlaceScores 0 c
        numVictories <- nsum victories
        ntrace ("First round victories, candidate " ++ show c) numVictories (show::Integer->String)
        advances <- (NInteger.fromInteger $ fromIntegral $ numCandidates - 2) `leq` numVictories >>= embedFormula
        ntrace (show c ++ " advances") advances (show::Bool->String)
        assert $ makeOpposed advances (eliminations ! (1, c))

      -- Second stage elimination: Candidates who lose even once are
      -- out.  We can be tolerant of ties here, because for a
      -- candidate to be a unique winner requires that all others be
      -- eliminated.
      forM_ candidates $ \c -> do
        losses <- losses candidates firstPlaceScores 1 c
        ntrace ("Second round losses, candidate " ++ show c) losses (show::[Bool]->String)
        advances <- embedFormula $ fromListForm [[Not loss] | loss <- losses]
        ntrace (show c ++ " advances") advances (show::Bool->String)
        assert $ makeOpposed advances (eliminations ! (2, c))
      -- Target candidate still remains in round 2, with everyone else
      -- eliminated, and therefore wins.

      forM_ candidates $ \c -> do
        assert $ fromListForm [[(if c == target then neg else id) $
                                Merely $ eliminations ! (2, c)]]

{-
irvManipulation votes =
    let voterSet = [1..length votes]
        manipulatorSet = map (+length votes) [1..length votes + 1]
        ballots = voterSet ++ manipulatorSet
        candidates = extractCandidates votes
        positions = [0..length candidates - 1]
        rounds = [0..length candidates - 1]
        beats' = beats candidates ballots in
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
-}
