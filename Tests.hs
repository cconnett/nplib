module Main where

import Solvers
import BruteForceSolver
import SatSolvers

import ILPSAT
import ILPSATReduction
import Embeddings
import Utilities
import ReductionComponents
import Reductions

import Voting hiding (beats)
import Elections
import Manipulation
import DebugHelp

import Test.QuickCheck
import Control.Monad
import Control.Monad.Writer
import Control.Arrow
import Data.Maybe
import Data.List
import Data.Ord
import Data.Bits
import Debug.Trace
import System.Exit
import Text.Regex.Posix
import Text.Printf
import qualified Data.Map as M
import qualified Data.Set as S

flop (a,b) = (b,a)

aux a@(Auxiliary _ _ _ _) = Just a
aux p = Nothing

mode = RSat

prop_detrivializeEquivalence :: [Constraint Var] -> Bool
prop_detrivializeEquivalence problem = solve BruteForce problem == solve BruteForce (detrivialize problem)

prop_trivialIneqs :: Constraint Var -> Property
prop_trivialIneqs i@(Inequality (summands,b)) = b >= 0 ==> fromJust $ solve mode problem
    where problem = detrivialize [cleanInequality i]
prop_trivialIneqs (Formula f) = False ==> False

prop_assignmentWorks :: Constraint (Proposition Var) -> Property
prop_assignmentWorks i@(Inequality (summands, b)) =
    let (satisfiable, trueVars) = first fromJust $ solveA mode [cleanInequality i] in
    satisfiable ==> (sum $ map ((M.fromList (map (flop . (second problemToProposition)) summands)) M.!) trueVars) <= b

prop_assignmentWorks f@(Formula clauses) =
    let (satisfiable, trueVars) = first fromJust $ solveA mode [f] in
    satisfiable ==> all (satisfiedBy trueVars) clauses
        where satisfiedBy trueVars (Clause []) = True
              satisfiedBy trueVars (Clause clause) = any (propMatch trueVars) clause
              propMatch trueVars (Merely var) =      (Merely var)`elem`trueVars
              propMatch trueVars (Not    p  ) = not $ propMatch trueVars p

prop_noFloatingBits (problem::Problem Var) =
    let (sat, trueProps) = first fromJust $ solveA mode problem in
    sat ==>
    let falseProps = (allProps problem) \\ trueProps in
    not (null $ trueProps ++ falseProps) ==>
    let fb = floatingBits problem in
    --(trace $ "floatingBits: " ++ show fb) $
    null fb
    {-
    not $ solve mode $ [(unsatisfiable $ embedConstraint "opposite" $ toSAT problem),
                        traceIt (Formula (map (Clause . (:[])      ) (filter (not . isAux) trueProps))),
                        traceIt (Formula (map (Clause . (:[]) . neg) (filter (not . isAux) falseProps)))]
     -}

prop_bruteForceAgreement :: Constraint Var -> Property
prop_bruteForceAgreement c =
    classify (bfResult == True) "SAT" $
    classify (bfResult == False) "UNSAT" $
    fromJust (solve mode [c]) == bfResult
    where bfResult = fromJust $ solve BruteForce [c]

prop_multipleConstraints :: Property
prop_multipleConstraints = forAll multiConstraintProblem $ \p ->
    let bfResult = fromJust $ solve BruteForce p in
    classify (bfResult == True) "SAT" $
    classify (bfResult == False) "UNSAT" $
    fromJust (solve mode (p::[Constraint Var])) == bfResult

{-
prop_manipNumbers election = minimumManipulators (possibleWinnersByBruteForce (read "borda")) election ==
                             minimumManipulators (possibleWinnersBySolver GLPK (read "borda")) election
-}
prop_doubleNegation prop = prop == (neg $ neg $ prop)

e = (liftM head) $
    readElections "/home/chris/schoolwork/thesis/elections/u-3-5"

showAllTrues x = putStr $ unlines $ map show2 $ snd $ solveA mode $ [conjoin $ toSAT x]
freeTrues x = map fromProposition $ filter isPos $ snd $ solveA mode $ x
reportIntermediateValues x = assignmentInterpretation (snd $ solveA mode $ [conjoin $ toSAT [x]]) x

summarizeElection manipulators trueProps allTheProps =
    let print = tell . (++"\n") . show
        putStrLn = tell . (++"\n") in execWriter $ do
  let falseProps = allTheProps \\ trueProps
  let trueVoteData = map fromProposition $
                     filter (\prop -> (not . isAux) prop && (not . isSurrogate) prop) $
                     trueProps
  let votes = reconstructVotes trueVoteData
  let survivors = calculateSurvivors trueVoteData
  let surrStatus = map (\s -> (s, "1")) $ sortBy (comparing sTag) $
                   filter (not . (== "") . sTag) $
                   filter isSurrogate $
                   trueProps
  let surrStatusFalse  = map (\s -> (s, "0")) $ sortBy (comparing sTag) $
                         filter (not . (== "") . sTag) $
                         filter isSurrogate $
                         falseProps
  let pointStatus = filter (("point " `isPrefixOf`) . sTag) $
                    filter isSurrogate $ 
                    trueProps
  let pointStatusFalse = filter (("point " `isPrefixOf`) . sTag) $
                         filter isSurrogate $
                         falseProps
  putStrLn "Non-manipulator Votes:"
  mapM_ print $ sort (take (length votes - manipulators) votes)
  putStrLn "Manipulator Votes:"
  mapM_ print $ sort (drop (length votes - manipulators) votes)
  putStrLn "Survivors at the beginning of each round:"
  mapM_ print survivors
  putStrLn "Surrogate info:"
  mapM_ (\(a,b) -> putStrLn $ a ++ " " ++ b) $ map ((second show) . flop) $ (mergeBy (sTag . fst) surrStatus surrStatusFalse)
  putStrLn "Point info:"
  mapM_ print pointStatus
      
reconstructVotes trueVoteData =
    [let candidates = sortNub $ map pwCandidateA $ filter isPairwiseDatum $ trueVoteData
         rankings = filter (\pwd -> pwVoter pwd == v) $
                    filter isPairwiseDatum $
                    trueVoteData
     in sortBy (\c1 c2 -> if (PairwiseDatum v c1 c2) `elem` trueVoteData
                          then LT else GT) candidates
         | v <- voters, (Counts v) `elem` trueVoteData]
    where voters = [1..maximum (map pwVoter $ filter isPairwiseDatum trueVoteData)]
calculateSurvivors tvd = [filter (not . (isEliminated r)) candidates | r <- [0..2]]
    where candidates = nub $ map pwCandidateA $ filter isPairwiseDatum tvd
          isEliminated r c = not $ null $
                             filter (\elimination -> eCandidate elimination == c && eRound elimination == r) $
                             filter isElimination tvd

 {-
prop_nestedInequalities (constraints' :: [Constraint Var]) =
    let constraints = map (\(c, i) -> fmap (\var -> (var, i)) c) (zip constraints' [0..]) in
    length constraints <= 10 ==>
    let numSatisfiable = length (filter (solve ZChaff . (:[])) constraints) in
    trace ("numSatisfiable: " ++ show numSatisfiable) $
          (--traceIt $
           solve ZChaff $
           embedConstraints (map show constraints) constraints $ \surrogates ->
               [Inequality ([(-1, propositionToProblem surrogate)
                                 | surrogate <- surrogates], -numSatisfiable)])
          && (--traceIt $
              not $
          (solve ZChaff $
           embedConstraints (map show constraints) constraints $ \surrogates ->
               [Inequality ([(-1, propositionToProblem surrogate)
                                 | surrogate <- surrogates], -(numSatisfiable+1))]))
-}
getSummary election = do
  let manipulators = 1
  let solver = possibleWinnersBySolverDebug RSat pluralityWithRunoffManipulation election
  let (sat, trueProps) = first fromJust $ solver manipulators election (Candidate 1)

  let summary = summarizeElection manipulators trueProps []
  if not sat then
        return "UNSAT"
     else
        return summary

main = do
  election <- e
  s <- getSummary election
  --print $ possibleWinnersBySolver Minisat pluralityWithRunoffManipulation election 1 election
  --let (p1, p2) = (pluralityWithRunoffManipulation election)
  --let p = p1 ++ p2 election 1 (Candidate 1)
  --writeFile "theProblem" (show p)
  writeFile "problemSummary1" s

{-
main = do
  (problem, allTheProps, sat, trueProps, falseProps, trueVoteData) <- setup
  unless sat $ do {putStrLn "UNSAT"; exitWith (ExitFailure 1)}
  print trueVoteData
  --Print non-unique surrogate tags:
  --print $ map (sTag . head) $ filter ((>1) . length) $ map sortNub $ groupBy (equating sTag) $ sortBy (comparing sTag) $ filter isSurrogate $ allTheProps
  summarizeIRVElection trueProps falseProps trueVoteData
  --print problem
-}