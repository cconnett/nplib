module ReductionComponents where

import Voting hiding (beats)
import qualified Voting (beats)
import ILPSAT
import ILPSATReduction
import Embeddings
import Hash

import Data.List

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
    
-- Non-manipulators' positional votes, directly encoded.
nonManipulatorPositionalVotes votes voterSet candidates positions =
    [Formula $ Clause [Merely $ VoteDatum voter candidate correctPosition] :
               [Clause [neg $ Merely $ VoteDatum voter candidate position]
                    | position <- positions, position /= correctPosition]
     | (voter, vote) <- zip voterSet votes,
       (candidate, correctPosition) <- zip (fromVote vote) positions]

nonManipulatorPairwiseVotes votes voterSet candidates =
    [Formula [Clause [(if Voting.beats vote candidateA candidateB then id else neg) $
                      Merely $ PairwiseDatum voter candidateA candidateB]]
         | (voter, vote) <- zip voterSet votes,
           candidateA <- candidates,
           candidateB <- candidates,
           candidateA /= candidateB]
    
-- Manipulator vote constraints (no two candidates in same position).
manipulatorPositionalPositionInjection manipulatorSet candidates positions =
    [Formula
     [Clause [neg $ Merely (VoteDatum manipulator a position), neg $ Merely (VoteDatum manipulator b position)]
          | manipulator <- manipulatorSet,
            a <- candidates, b <- candidates, a /= b,
            position <- positions]]

-- Manipulator vote constraints (every candidate in some position).
manipulatorPositionalPositionSurjection manipulatorSet candidates positions =
    [Formula
     [Clause [Merely (VoteDatum manipulator c position) | position <- positions]
          | manipulator <- manipulatorSet, c <- candidates]]

-- NB: that no candidate is in more than one position is implied by
-- the previous two constraints.  (Injection + Surjection = 1-to-1)

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

-- Basic constraints for voting rules using elimination.
eliminationBasics candidates rounds =
    -- Everyone's in to start (all eliminations for round 0 are false)
    [Formula [Clause [neg $ Merely (Eliminated 0 candidate)] | candidate <- candidates]] ++
    -- Cascading elimination status
    [Formula [Clause [neg $ Merely (Eliminated  round    candidate),
                            Merely (Eliminated (round+1) candidate)]
              | round <- tail $ init $ rounds, -- No eliminations in the first or last rounds.
                candidate <- candidates]]

-- Every ballot must give a point to one candidate and only one candidate in all but the last round.
firstPlacePoints candidates ballots rounds =
        (concat [points candidates candidates [v] [r] $ \pointCsVR -> [Formula [Clause pointCsVR]]
                 | v <- ballots,
                   r <- init rounds]) ++
        (concat [point candidates a v r $ \pointAVR ->
                 point candidates b v r $ \pointBVR ->
                     [Formula [Clause [neg $ pointAVR, neg $ pointBVR]]]
                 | v <- ballots,
                   r <- init rounds,
                   a <- candidates,
                   b <- candidates, a < b])
    
-- IRV related embeddings
beats candidates ballots
       a b r = embedProblem (show a ++ " beats " ++ show b ++ " in round " ++ show r) $
               points candidates [b] ballots [r] $ \bPoints ->
               points candidates [a] ballots [r] $ \aPoints ->
                       (Formula [Clause [neg $ Merely $ Eliminated r b]] :
                        Formula [Clause [neg $ Merely $ Eliminated r a]] :
                        (trans ineqNumber $
                         --(\ineq -> unsafePerformIO (do {writeFile ("ineqDump"++show a ++ show b ++ show r) (show ineq); return ineq})) $
                         Inequality ([( 1, bPoint) | bPoint <- bPoints] ++
                                     [(-1, aPoint) | aPoint <- aPoints], -1)) ++
                       [])
    where --ineqNumber = (10^9 + (fromCandidate a*10^6) + (fromCandidate b*10^3) + r)
          ineqNumber = fromIntegral $ hash (show a ++ show b ++ show r)

points candidates cs vs rs = pluralizeEmbedding [point candidates c v r | c <- cs, v <- vs, r <- rs]
point candidates c v r = embedConstraint ("point " ++ show r ++ " " ++ show c ++ " " ++ show v) $
                         conjoin $
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
shouldBeEliminated allOthersEliminated victories
                   r c = (embedConstraint (show c ++ " should be eliminated for round " ++ show (r+1))
                         (Formula $ Clause [neg allOthersEliminated] :
                          [Clause [neg victory] | victory <- victories]) ) -- :: Embedding (VoteDatum a)

--fullShouldBeEliminated :: [Candidate a] -> [Int] -> Int -> Candidate a -> Embedding (VoteDatum a)
fullShouldBeEliminated candidates ballots
                       r c lambda = allOthersEliminated candidates r c $ \aoe ->
                                    victories candidates ballots r c $ \vics ->
                                    shouldBeEliminated aoe vics r c lambda

-- Copeland voting components
pairwiseVictory ballots c d =
    let tag = (show c ++ " defeats " ++ show d) in
    embedProblem tag (trans (fromIntegral $ hash tag) $
                      Inequality ([(-1, Merely $ PairwiseDatum v c d) | v <- ballots] ++
                                  [( 1, Merely $ PairwiseDatum v d c) | v <- ballots], -1))
pairwiseTie ballots c d =
    embedProblem (show c ++ " ties " ++ show d) $
    pairwiseVictory ballots c d $ \cBeatsD ->
    pairwiseVictory ballots d c $ \dBeatsC ->
    [Formula [Clause [neg cBeatsD], Clause [neg dBeatsC]]]

copelandScoreBetter candidates ballots c d =
    pluralizeEmbedding [pairwiseVictory ballots d e | e <- delete d candidates] $ \dVics ->
    pluralizeEmbedding [pairwiseVictory ballots c e | e <- delete c candidates] $ \cVics ->
    pluralizeEmbedding [pairwiseTie     ballots d e | e <- delete d candidates] $ \dTies ->
    pluralizeEmbedding [pairwiseTie     ballots c e | e <- delete c candidates] $ \cTies ->
    trans (fromIntegral $ hash (show c ++ "'s copeland score is better than " ++ show d ++ "'s")) $
    Inequality ([( 2, dVic) | dVic <- dVics] ++
                [(-2, cVic) | cVic <- cVics] ++
                [( 1, dTie) | dTie <- dTies] ++
                [(-1, cTie) | cTie <- cTies],
                 -1)
