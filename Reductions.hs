{-# LANGUAGE TypeSynonymInstances #-}

module Reductions where

import Control.Monad
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

type ManipulationProblem = [Vote Int] -> Int -> Candidate Int -> InstanceBuilder ()
instance Read (ManipulationProblem)  where
    readsPrec _ "plurality" = [(scoringProtocolManipulation (\n -> 1:(repeat 0)), "")]
    readsPrec _ "pluralityWithRunoff" = [(pluralityWithRunoffManipulation, "")]
    readsPrec _ "borda" = [(scoringProtocolManipulation (\n -> [n-1,n-2..0]), "")]
    readsPrec _ "veto" = [(scoringProtocolManipulation (\n -> replicate (n-1) 1 ++ [0]), "")]
    readsPrec _ "irv" = [(irvManipulation, "")]
    readsPrec _ "copeland" = [(copelandManipulation (1%2), "")]
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

      ntrace "FirstPlaceScores" firstPlaceScores
      ntrace "EliminationData" eliminations
      manipulatorPairwiseBeatsASAR (drop numNonmanipulators ballots) candidates
      manipulatorPairwiseBeatsTotal (drop numNonmanipulators ballots) candidates

      -- First round elimination: The candidates who advance are
      -- exactly those who have at least |C| - 2 victories
      forM_ candidates $ \c -> do
        victories <- victories candidates firstPlaceScores 0 c
        numVictories <- nsum victories
        ntrace ("First round victories, candidate " ++ show c) numVictories
        advances <- (NInteger.fromInteger $ fromIntegral $ numCandidates - 2) `leq` numVictories >>= embedFormula
        ntrace (show c ++ " advances") advances
        assert $ makeOpposed advances (eliminations ! (1, c))

      -- Second stage elimination: Candidates who lose even once are
      -- out.  We can be tolerant of ties here, because for a
      -- candidate to be a unique winner requires that all others be
      -- eliminated.
      forM_ candidates $ \c -> do
        losses <- losses candidates firstPlaceScores 1 c
        ntrace ("Second round losses, candidate " ++ show c) losses
        advances <- embedFormula $ fromListForm [[Not loss] | loss <- losses]
        ntrace (show c ++ " advances") advances
        assert $ makeOpposed advances (eliminations ! (2, c))

      -- Target candidate still remains in round 2, with everyone else
      -- eliminated, and therefore wins.
      forM_ candidates $ \c -> do
        assert $ fromListForm [[(if c == target then neg else id) $
                                Merely $ eliminations ! (2, c)]]


irvManipulation votes numManipulators target =
  let numNonmanipulators = length votes
      candidates = sort $ extractCandidates votes
      candRange = (head candidates, last candidates)
      numCandidates = length candidates
      rounds = [0 .. length candidates - 1] in
    do
      ballots <- makePairwiseBallots votes candRange numManipulators
      eliminations <- makeEliminations rounds candidates
      firstPlaceScores <- getFirstPlaceScores ballots candRange eliminations rounds

      ntrace "FirstPlaceScores" firstPlaceScores
      ntrace "EliminationData" eliminations
      manipulatorPairwiseBeatsASAR (drop numNonmanipulators ballots) candidates
      manipulatorPairwiseBeatsTotal (drop numNonmanipulators ballots) candidates

      -- Elimination: We protect candidates who strictly beat another
      -- non-eliminated candidate, and also force out all candidates
      -- who do not meet this criterion.  Both sides are needed to
      -- deny the SAT solver any liberty in deciding who is eliminated
      -- (by means other than selecting manipulator ballots).  For
      -- every pair of distinct candidates in a given round where both
      -- are still in, if one strictly beats the other, that candidate
      -- is protected from elimination.
      forM_ (init rounds) $ \round -> do { -- We only perform eliminations up to the last round.
        forM_ candidates $ \candidate -> do
          victories <- victories candidates firstPlaceScores round candidate
          onlyOneLeft <- embedFormula $ fromListForm
                         [[(if other == candidate then Not else Merely) $ eliminations ! (round, other)]
                               | other <- candidates]
          ntrace "Only one left" onlyOneLeft

          -- Advance this candidate it beat someone who's not
          -- eliminatoed or if it's the only one left.
          nonEliminatedVictories <- embedFormulas $
                                    [fromListForm [[Merely victory], [Not $ eliminations ! (round, opponent)]]
                                     | (victory, opponent) <- zip victories (delete candidate candidates)]
          ntrace ("Round " ++ show round ++ " non-elim victories, " ++ show candidate) nonEliminatedVictories
          advances <- embedFormula $ fromListForm [map Merely $ onlyOneLeft : nonEliminatedVictories]
          ntrace (show candidate ++ " advances") advances
          assert $ makeOpposed advances (eliminations ! (round+1, candidate)) }

      -- Target candidate still remains after |C| - 1 rounds, with
      -- everyone else eliminated, and therefore wins.
      forM_ candidates $ \c -> do
        assert $ fromListForm [[(if c == target then neg else id) $
                                Merely $ eliminations ! (last rounds, c)]]


copelandManipulation tieValue votes numManipulators target =
    let numNonmanipulators = length votes
        candidates = sort $ extractCandidates votes
        candRange = (head candidates, last candidates) in
    do
      ballots <- makePairwiseBallots votes candRange numManipulators
      manipulatorPairwiseBeatsASAR (drop numNonmanipulators ballots) candidates
      manipulatorPairwiseBeatsTotal (drop numNonmanipulators ballots) candidates

      pairwiseScores <- getPairwiseScores candRange ballots
      ntrace "Pairwise Scores" pairwiseScores
      copelandScores <- getCopelandScores tieValue pairwiseScores candRange
      ntrace "Copeland Scores" copelandScores

      forM_ (delete target candidates) $ \opponent -> do
        (copelandScores ! target) `gt` (copelandScores ! opponent) >>= assert
