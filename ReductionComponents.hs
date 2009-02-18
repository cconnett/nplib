module ReductionComponents where

import Control.Monad
import Data.Array.IArray
import Data.Ix
import Data.List
import Data.Maybe
import Data.Ord
import Data.Ratio
import Embeddings
import SAT
import NInteger
import NPLib
import Utilities
import Voting hiding (beats)
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Voting (beats)

import Tracing

-- Reductions of manipulation instances for specific classes of voting
-- rules to mixed SAT and ILP problem instance.
data VoteDatum a = VoteDatum {vdVoter :: Int, vdCandidate :: Candidate a, vdPosition :: Int}
                 | PairwiseDatum {pwVoter :: Int, pwCandidateA, pwCandidateB :: Candidate a}
                 | Eliminated {eRound :: Int, eCandidate :: Candidate a}
    deriving (Show, Read, Eq, Ord)
isVoteDatum (VoteDatum _ _ _) = True
isVoteDatum _ = False
isPairwiseDatum (PairwiseDatum _ _ _) = True
isPairwiseDatum _ = False
isElimination (Eliminated _ _) = True
isElimination _ = False

newtype Position = Position Int
    deriving (Show, Eq, Ord, Ix)
type Round = Int

type PositionalBallot = Array (Candidate Int, Position) Var
type PairwiseBallot = Array (Candidate Int, Candidate Int) Var
type EliminationData = Array (Round, Candidate Int) Var

showPositionalBallot :: Array (Candidate Int, Position) Bool -> String
showPositionalBallot dballot =
    let trueAssocs :: [(Candidate Int, Position)] = map fst $ filter snd (assocs dballot)
        candidates :: [Candidate Int] = sortNub $ map fst trueAssocs
        position :: Candidate Int -> Position
        position candidate = fromJust $ lookup candidate trueAssocs
    in show $ map fromCandidate $ sortBy (comparing position) candidates

showPairwiseBallot :: Array (Candidate Int, Candidate Int) Bool -> String
showPairwiseBallot dballot =
    let candidates = sortNub $ map fst $ indices dballot
    in show $ map fromCandidate $ sortBy (\a b -> if dballot ! (a, b) then GT else LT) candidates

showEliminationData :: Array (Round, Candidate Int) Bool -> String
showEliminationData eliminations =
    let trueAssocs = map fst $ filter snd (assocs eliminations)
    in show trueAssocs
-- Non-manipulators' positional votes, directly encoded.
nonManipulatorPositionalVotes :: [Vote Int] -> [PositionalBallot] -> (Candidate Int, Candidate Int) ->
                                 (Position, Position) -> NProgramComputation ()
nonManipulatorPositionalVotes votes ballots candRange posRange =
    sequence_ [do
                assert $ makeTrue (ballots !! voter ! (candidate, correctPosition))
                assertAll [(makeFalse (ballots !! voter ! (candidate, position)))
                           | position <- range posRange, position /= correctPosition]
               | (voter, vote) <- zip [0..] votes,
                 (candidate, correctPosition) <- zip (fromVote vote) (range posRange)]

nonManipulatorPairwiseVotes :: [Vote Int] -> [PairwiseBallot] -> [Candidate Int] ->
                               NProgramComputation ()
nonManipulatorPairwiseVotes votes ballots candidates =
    assertAll [(if Voting.beats vote candidateA candidateB then makeTrue else makeFalse)
               (ballots !! voter ! (candidateA, candidateB))
              | (voter, vote) <- zip [0..] votes,
                candidateA <- candidates,
                candidateB <- candidates,
                candidateA /= candidateB]

-- Manipulator vote constraints (no two candidates in same position).
manipulatorPositionalPositionInjection :: [PositionalBallot] -> (Candidate Int, Candidate Int) ->
                                          (Position, Position) -> NProgramComputation ()
manipulatorPositionalPositionInjection manipulatorBallots candRange posRange =
    assert $ fromListForm
    [[Not (ballot ! (a, position)), Not (ballot ! (b, position))]
         | ballot <- manipulatorBallots,
           a <- range candRange, b <- range candRange, a /= b,
           position <- range posRange]

-- Manipulator vote constraints (every candidate in some position).
manipulatorPositionalPositionSurjection :: [PositionalBallot] -> (Candidate Int, Candidate Int) ->
                                           (Position, Position) -> NProgramComputation ()
manipulatorPositionalPositionSurjection manipulatorBallots candRange posRange =
    assert $ fromListForm $ concat
    [[[Merely (ballot ! (c, position)) | position <- range posRange]]
     | ballot <- manipulatorBallots,
       c <- range candRange]

-- NB: that no candidate is in more than one position is implied by
-- the previous two constraints.  (Injection + Surjection = 1-to-1)

-- Pairwise beat relationship is anti-symmetric and anti-reflexive
manipulatorPairwiseBeatsASAR :: [PairwiseBallot] -> [Candidate Int] -> NProgramComputation ()
manipulatorPairwiseBeatsASAR manipulatorBallots candidates =
    assert $ fromListForm $ concat
    [[[Not (ballot ! (candidateA, candidateB)),
       Not (ballot ! (candidateB, candidateA))]
      | ballot <- manipulatorBallots,
        candidateA <- candidates,
        candidateB <- candidates,
        candidateA <= candidateB]]

-- Pairwise beat relationship is total
manipulatorPairwiseBeatsTotal :: [PairwiseBallot] -> [Candidate Int] -> NProgramComputation ()
manipulatorPairwiseBeatsTotal manipulatorBallots candidates =
    assert $ fromListForm $ concat
    [[[Merely (ballot ! (candidateA, candidateB)),
       Merely (ballot ! (candidateB, candidateA))]
      | ballot <- manipulatorBallots,
        candidateA <- candidates,
        candidateB <- candidates,
        candidateA < candidateB]]

-- Basic constraints for voting rules using elimination.
eliminationBasics :: EliminationData -> [Candidate Int] -> [Round] -> NProgramComputation ()
eliminationBasics eliminations candidates rounds = do
    -- Everyone's in to start (all eliminations for round 0 are false)
    assertAll [makeFalse (eliminations ! (0, candidate))
               | candidate <- candidates]
    -- Cascading elimination status
    assertAll [(eliminations ! (round, candidate)) `implies`
               (eliminations ! (round + 1, candidate))
               | round <- tail $ init $ rounds, -- No eliminations in the first or last rounds.
                 candidate <- candidates]

-- Every ballot must give a point to one candidate and only one
-- candidate in all but the last round.
firstPlacePoints candidates eliminations ballots rounds = do
  forM_ ballots $ \ballot -> do
    forM_ (init rounds) $ \round -> do
      pointsCsVR <- points candidates eliminations candidates [ballot] [round]
      assert $ fromListForm [map Merely pointsCsVR]
  sequence [do
             pointAVR <- point candidates eliminations a v r
             pointBVR <- point candidates eliminations b v r
            -- Giving a point to neither a nor b doesn't run afoul of
            -- this rule, so we don't need to check if the ballot
            -- counts.
             assert $ fromListForm [[Not pointAVR, Not pointBVR]]
            | v <- ballots,
              r <- init rounds,
              a <- candidates,
              b <- candidates, a < b]

makePositionalBallots :: [Vote Int] -> (Candidate Int, Candidate Int) ->
                         (Position, Position) -> Int -> NProgramComputation [PositionalBallot]
makePositionalBallots votes candRange posRange numManipulators =
    let numCandidates = rangeSize candRange
        numNonmanipulators = length votes
        numVoters = numNonmanipulators + numManipulators
        numPositions = rangeSize posRange
    in do
      ballots <- replicateM numVoters (liftM (listArray (crossRanges candRange posRange)) $
                                             takeSatVars (numCandidates * numPositions))
      let manipulatorBallots = drop numNonmanipulators ballots
      let nonManipulatorBallots = take numNonmanipulators ballots
      manipulatorPositionalPositionInjection manipulatorBallots candRange posRange
      manipulatorPositionalPositionSurjection manipulatorBallots candRange posRange
      nonManipulatorPositionalVotes votes nonManipulatorBallots candRange posRange
      return ballots

makePairwiseBallots :: [Vote Int] -> (Candidate Int, Candidate Int) -> Int ->
                       NProgramComputation [PairwiseBallot]
makePairwiseBallots votes candRange numManipulators =
    let numCandidates = rangeSize candRange
        numNonmanipulators = length votes
        numVoters = numNonmanipulators + numManipulators
        candidates = range candRange
    in do
      ballots <- replicateM numVoters (liftM (listArray (crossRanges candRange candRange)) $
                                              takeSatVars (numCandidates * numCandidates))

      let manipulatorBallots = drop numNonmanipulators ballots
      let nonManipulatorBallots = take numNonmanipulators ballots

      manipulatorPairwiseBeatsASAR manipulatorBallots candidates
      manipulatorPairwiseBeatsTotal manipulatorBallots candidates
      nonManipulatorPairwiseVotes votes nonManipulatorBallots candidates

      return ballots

makeEliminations :: [Round] -> [Candidate Int] -> NProgramComputation EliminationData
makeEliminations rounds candidates = do
    let candRange = (head candidates, last candidates)
    let roundRange = (head rounds, last rounds)
    eliminations <- liftM (listArray (crossRanges roundRange candRange)) $
                    takeSatVars (rangeSize roundRange * rangeSize candRange)
    eliminationBasics eliminations candidates rounds
    return eliminations

--Scoring protocol related embeddings
getScore :: [PositionalBallot] -> [Int] -> (Position, Position) -> [Int] -> Candidate Int -> NProgramComputation NInteger
getScore ballots voters posRange scoreList candidate = do
  scores <- sequence [mul1bit (NInteger.fromInteger $ fromIntegral $ (scoreList !! index posRange position) :: NInteger)
                              (ballots !! voter ! (candidate, position))
                     | voter <- voters,
                       position <- range posRange]
  nsum scores


-- IRV and pluralityWithRunoff embeddings

-- beats: return a formula that states a's first place point score is
-- higher than b's in round r, respecting eliminations
beats :: [Candidate Int] -> [PairwiseBallot] -> EliminationData ->
         Candidate Int -> Candidate Int -> Round -> NProgramComputation Formula
beats candidates ballots eliminations
      a b r = do
        aPoints <- points candidates eliminations [a] ballots [r]
        bPoints <- points candidates eliminations [b] ballots [r]
        ntrace ("Round " ++ show r ++ ", " ++ show a ++ " points") aPoints (show::[Bool]->String)
        aScore <- nsum aPoints
        bScore <- nsum bPoints
        ntrace ("Round " ++ show r ++ ", " ++ show a ++ " score") aScore (show::Int->String)
        aBeatsB <- bScore `lt` aScore >>= embedFormula
        return $ fromListForm [[Merely $ eliminations ! (r, a),
                                Merely $ eliminations ! (r, b),
                                Merely $ aBeatsB]]

points :: [Candidate Int] -> EliminationData ->
          [Candidate Int] -> [PairwiseBallot] -> [Round] -> NProgramComputation [Var]
points candidates eliminations cs ballots rs =
    sequence [point candidates eliminations c ballot r | c <- cs, ballot <- ballots, r <- rs]
point :: [Candidate Int] -> EliminationData ->
         Candidate Int -> PairwiseBallot -> Round -> NProgramComputation Var
point candidates eliminations c ballot round =
    embedFormula $ fromListForm $ concat $
                     --[[Merely (Counts v)],
                     [[Not $ eliminations ! (round, c)]] :
                     [[[Merely $ ballot ! (c, d), Merely $ eliminations ! (round, d)]]
                          | d <- delete c candidates]
{-
allOthersEliminated :: [Candidate Int] -> EliminationData -> Round -> Candidate a -> Embedding a
allOthersEliminated candidates eliminations
                    r c = embedFormula $ fromListForm
                          [[(if a == c then neg else id) $ Merely $ eliminations ! (r, a)]
                               | a <- candidates]
-}
victories, losses :: [Candidate Int] -> [PairwiseBallot] -> EliminationData ->
                     Round -> Candidate Int -> NProgramComputation [Var]
victories candidates ballots eliminations
          r c = sequence [beats candidates ballots eliminations c a r >>= embedFormula
                              | a <- delete c candidates]
losses candidates ballots eliminations
       r c = forM (delete c candidates) $ \a -> do
               aBeatsC <- beats candidates ballots eliminations a c r >>= embedFormula
               embedFormula $ fromListForm [[Merely $ eliminations ! (r, c), Merely aBeatsC]]

{-
-- shouldBeEliminated: candidate c should be eliminated for round r + 1
shouldBeEliminated :: Proposition (VoteDatum Int) -> [Proposition (VoteDatum Int)] ->
                      Int -> Candidate Int -> NProgramComputation Var
shouldBeEliminated allOthersEliminated victories =
    makeFalse allOthersEliminated
    mapM (assert . makeFalse) victories
-}
{-
-- Copeland voting components
pairwiseVictory ballots c d =
    let tag = (show c ++ " defeats " ++ show d) in
    embedProblem' tag $ trans (fromIntegral $ hash tag) $
                  Inequality ([(-1, [Formula [Clause [Merely $ Counts v],
                                              Clause [Merely $ PairwiseDatum v c d]]]) | v <- ballots] ++
                              [( 1, [Formula [Clause [Merely $ Counts v],
                                              Clause [Merely $ PairwiseDatum v d c]]]) | v <- ballots], -1)
pairwiseTie pvm c d =
    let cBeatsD = fst $ pvm M.! (c,d)
        dBeatsC = fst $ pvm M.! (d,c)
    in
      embedProblem (show c ++ " ties " ++ show d) $
    [Formula [Clause [neg cBeatsD], Clause [neg dBeatsC]]]
makePairwiseVictoryMap candidates ballots =
    M.fromList $ [((c,d), pairwiseVictory ballots c d) | c <- candidates, d <- candidates, c /= d]

copelandScoreBetter tieValue pvm candidates c d =
    let wt = numerator tieValue
        ww = denominator tieValue
        tag = (show c ++ " has a better copeland score than " ++ show d)
        dVics = [fst $ pvm M.! (d,e) | e <- delete d candidates]
        cVics = [fst $ pvm M.! (c,e) | e <- delete c candidates]
    in
      embedProblem tag $
       pluralizeEmbedding [pairwiseTie pvm d e | e <- delete d candidates] $ \dTies ->
       pluralizeEmbedding [pairwiseTie pvm c d | e <- delete c candidates] $ \cTies ->
       trans (fromIntegral $ hash (show c ++ "'s copeland score is better than " ++ show d ++ "'s")) $
       Inequality ([( ww, makeTrue dVic) | dVic <- dVics] ++
                   [(-ww, makeTrue cVic) | cVic <- cVics] ++
                   [( wt, makeTrue dTie) | dTie <- dTies] ++
                   [(-wt, makeTrue cTie) | cTie <- cTies],
                   -1)
-}