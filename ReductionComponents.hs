module ReductionComponents where

import Control.Monad
import Data.Array.IArray
import Data.Ix
import Data.List
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

type PositionalBallot = Array (Candidate Int, Position) Var
type PairwiseBallot = Array (Candidate Int, Candidate Int) Var

showPositionalBallot :: Array (Candidate Int, Position) Bool -> String
showPositionalBallot dballot =
    let trueAssocs = filter snd (assocs dballot)
        candidates = sortNub $ map fst trueAssocs
        position candidate = lookup candidate trueAssocs
    in show $ map (fromCandidate . fst) $ sortBy (comparing position) candidates

showPairwiseBallot :: Array (Candidate Int, Candidate Int) Bool -> String
showPairwiseBallot dballot =
    let candidates = sortNub $ map fst $ indices dballot
    in show $ map fromCandidate $ sortBy (\a b -> if dballot ! (a, b) then GT else LT) candidates

-- Non-manipulators' positional votes, directly encoded.
nonManipulatorPositionalVotes :: [Vote Int] -> [PositionalBallot] -> (Candidate Int, Candidate Int) ->
                                 (Position, Position) -> Stateful ()
nonManipulatorPositionalVotes votes ballots candRange posRange =
    sequence_ [do
                assert $ makeTrue (ballots !! voter ! (candidate, correctPosition))
                assertAll [(makeFalse (ballots !! voter ! (candidate, position)))
                           | position <- range posRange, position /= correctPosition]
               | (voter, vote) <- zip [0..] votes,
                 (candidate, correctPosition) <- zip (fromVote vote) (range posRange)]
{-
nonManipulatorPairwiseVotes :: [Vote (Candidate a)] -> [Ballot] -> [Int] -> Stateful ()
nonManipulatorPairwiseVotes votes ballots candidates =
    assertAll [(if Voting.beats vote (Candidate $ candidateA+1) (Candidate $ candidateB+1) then makeTrue else makeFalse)
               (ballots !! voter !! candidateA !! candidateB)
              | (voter, vote) <- zip [0..] votes,
                candidateA <- candidates,
                candidateB <- candidates,
                candidateA /= candidateB]
-}
-- Manipulator vote constraints (no two candidates in same position).
manipulatorPositionalPositionInjection :: [PositionalBallot] -> (Candidate Int, Candidate Int) ->
                                          (Position, Position) -> Stateful ()
manipulatorPositionalPositionInjection manipulatorBallots candRange posRange =
    assert $
    Formula [Clause [Not (ballot ! (a, position)), Not (ballot ! (b, position))]
             | ballot <- manipulatorBallots,
               a <- range candRange, b <- range candRange, a /= b,
               position <- range posRange]

-- Manipulator vote constraints (every candidate in some position).
manipulatorPositionalPositionSurjection :: [PositionalBallot] -> (Candidate Int, Candidate Int) ->
                                           (Position, Position) -> Stateful ()
manipulatorPositionalPositionSurjection manipulatorBallots candRange posRange =
    assertAll $
    [Formula [Clause [Merely (ballot ! (c, position)) | position <- range posRange]]
     | ballot <- manipulatorBallots,
       c <- range candRange]

-- NB: that no candidate is in more than one position is implied by
-- the previous two constraints.  (Injection + Surjection = 1-to-1)
{-
-- Pairwise beat relationship is anti-symmetric and anti-reflexive
manipulatorPairwiseBeatsASAR manipulatorSet candidates =
    [Formula [Clause [neg $ Merely (PairwiseDatum voter candidateA candidateB),
                      neg $ Merely (PairwiseDatum voter candidateB candidateA)]
              | voter <- manipulatorSet,
                candidateA <- candidates,
                candidateB <- candidates,
                candidateA <= candidateB]]

-- Pairwise beat relationship is total
manipulatorPairwiseBeatsTotal manipulatorSet candidates =
    [Formula [Clause [Merely (PairwiseDatum voter candidateA candidateB),
                      Merely (PairwiseDatum voter candidateB candidateA)]
              | voter <- manipulatorSet,
                candidateA <- candidates,
                candidateB <- candidates,
                candidateA < candidateB]]
-}
-- Basic constraints for voting rules using elimination.
eliminationBasics eliminations candidates rounds = do
    -- Everyone's in to start (all eliminations for round 0 are false)
    assertAll [makeFalse (eliminations !! 0 !! candidate)
               | candidate <- candidates]
    -- Cascading elimination status
    assertAll [(eliminations !!  round    !! candidate) `implies`
               (eliminations !! (round+1) !! candidate)
               | round <- tail $ init $ rounds, -- No eliminations in the first or last rounds.
                 candidate <- candidates]

-- Every ballot must give a point to one candidate and only one
-- candidate in all but the last round.
{-
firstPlacePoints candidates ballots rounds =
        (concat [points candidates candidates [v] [r] $
                 \pointCsVR -> [Formula [Clause $ (neg $ Merely $ Counts v) : pointCsVR]]
                 | v <- ballots,
                   r <- init rounds]) ++
        (concat [point candidates a v r $ \pointAVR ->
                 point candidates b v r $ \pointBVR ->
                 -- Giving a point to neither a nor b doesn't run
                 -- afoul of this rule, so we don't need to check if
                 -- the ballot counts.
                     [Formula [Clause [neg $ pointAVR, neg $ pointBVR]]]
                 | v <- ballots,
                   r <- init rounds,
                   a <- candidates,
                   b <- candidates, a < b])
-}

makePositionalBallots :: [Vote Int] -> (Candidate Int, Candidate Int) ->
                         (Position, Position) -> Int -> Stateful [PositionalBallot]
makePositionalBallots votes candRange posRange numManipulators =
    let numCandidates = rangeSize candRange
        numNonmanipulators = length votes
        numVoters = numNonmanipulators + numManipulators
        numPositions = rangeSize posRange
    in do
      ballots <- replicateM numVoters (liftM (listArray (crossRanges candRange posRange)) $
                                             takeSatVars (numCandidates*numPositions))
      let manipulatorBallots = drop numNonmanipulators ballots
      let nonManipulatorBallots = take numNonmanipulators ballots
      manipulatorPositionalPositionInjection manipulatorBallots candRange posRange
      manipulatorPositionalPositionSurjection manipulatorBallots candRange posRange
      nonManipulatorPositionalVotes votes nonManipulatorBallots candRange posRange
      return ballots
{-
makePairwiseBallots votes candidates numManipulators =
    let numCandidates = length candidates
        numNonmanipulators = length votes
        numVoters = numNonmanipulators + numManipulators
    in do
      ballots <- replicateM numVoters (replicateM numCandidates (takeSatVars numCandidates))

      let manipulatorBallots = drop numNonmanipulators ballots
      let nonManipulatorBallots = take numNonmanipulators ballots

      manipulatorPairwiseBeatsASAR manipulatorBallots candidates
      manipulatorPairwiseBeatsTotal manipulatorBallots candidates
      nonManipulatorPairwiseVotes votes nonManipulatorBallots candidates

      return ballots
-}
--Scoring protocol related embeddings
getScore :: [PositionalBallot] -> [Int] -> (Position, Position) -> [Int] -> Candidate Int -> Stateful NInteger
getScore ballots voters posRange scoreList candidate = do
  scores <- sequence [mul1bit (NInteger.fromInteger $ fromIntegral $ (scoreList !! index posRange position) :: NInteger)
                              (ballots !! voter ! (candidate, position))
                     | voter <- voters,
                       position <- range posRange]
  nsum scores

{-
-- IRV and pluralityWithRunoff embeddings
beats candidates ballots
       a b r = embedProblem (show a ++ " beats " ++ show b ++ " in round " ++ show r) $
               points candidates [b] ballots [r] $ \bPoints ->
               points candidates [a] ballots [r] $ \aPoints ->
                       (Formula [Clause [neg $ Merely $ Eliminated r b]] :
                        Formula [Clause [neg $ Merely $ Eliminated r a]] :
                        (trans ineqNumber $
                         --(\ineq -> unsafePerformIO (do {writeFile ("ineqDump"++show a ++ show b ++ show r) (show ineq); return ineq})) $
                         Inequality ([( 1, propositionToProblem bPoint) | bPoint <- bPoints] ++
                                     [(-1, propositionToProblem aPoint) | aPoint <- aPoints], -1)) ++
                       [])
    where --ineqNumber = (10^9 + (fromCandidate a*10^6) + (fromCandidate b*10^3) + r)
          ineqNumber = fromIntegral $ hash (show a ++ show b ++ show r)

points candidates cs vs rs = pluralizeEmbedding [point candidates c v r | c <- cs, v <- vs, r <- rs]
point candidates c v r = embedConstraint ("point " ++ show r ++ " " ++ show c ++ " " ++ show v) $
                         conjoin $
                         (Formula [Clause [Merely $ Counts v]]) :
                         (Formula [Clause [neg $ Merely $ Eliminated r c]]) :
                         ([Formula [Clause [Merely $ PairwiseDatum v c d, Merely $ Eliminated r d]]
                           | d <- delete c candidates])

--allOthersEliminated :: [Candidate a] -> Int -> Candidate a -> Embedding a
allOthersEliminated candidates
                    r c = embedConstraint ("all except " ++ show c ++ " eliminated in round " ++ show r)
                          (Formula [Clause [(if a == c then neg else id) $ Merely $ Eliminated r a] | a <- candidates])

victories candidates ballots
          r c = (pluralizeEmbedding [beats candidates ballots c a r | a <- delete c candidates])
losses candidates ballots
       r c = (pluralizeEmbedding [embedProblem (show c ++ " loses to " ++ show a)
                                               (beats candidates ballots a c r $ \aBeatsC ->
                                                [Formula [Clause [Merely $ Eliminated r c, aBeatsC]]])
                                      | a <- delete c candidates])

--shouldBeEliminated :: Proposition (VoteDatum Int) -> [Proposition (VoteDatum Int)] -> Int -> Candidate Int -> Embedding (VoteDatum Int)
shouldBeEliminated allOthersEliminated victories =
--                   r c = (embedConstraint (show c ++ " should be eliminated for round " ++ show (r+1))
                         makeFalse allOthersEliminated >>= assert
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