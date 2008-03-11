module Main where

import Solvers
import ZChaffSolver
import GLPKSolver
import BruteForceSolver

import ILPSAT
import ILPSATReduction
import Embeddings
import Utilities

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

mode = ZChaff

prop_detrivializeEquivalence :: [Constraint Var] -> Bool
prop_detrivializeEquivalence problem = solve BruteForce problem == solve BruteForce (detrivialize problem)

prop_trivialIneqs :: Constraint Var -> Property
prop_trivialIneqs i@(Inequality (summands,b)) = b >= 0 ==> solve mode problem
    where problem = detrivialize [cleanInequality i]
prop_trivialIneqs (Formula f) = False ==> False

prop_assignmentWorks :: Constraint (Proposition Var) -> Property
prop_assignmentWorks i@(Inequality (summands, b)) =
    --let cleanI = Inequality (map (second normalizeProposition) summands, b) in
    let (satisfiable, trueVars) = solveA mode [cleanInequality i] in
    satisfiable ==> (sum $ mapMaybe ((flip M.lookup) (M.fromList (map flop summands))) trueVars) <= b

prop_assignmentWorks f@(Formula clauses) =
    let (satisfiable, trueVars) = solveA mode [f] in
    satisfiable ==> all (satisfiedBy trueVars) clauses
        where satisfiedBy trueVars (Clause []) = True
              satisfiedBy trueVars (Clause clause) = any (propMatch trueVars) clause
              propMatch trueVars (Merely var) =      (Merely var)`elem`trueVars
              propMatch trueVars (Not    p  ) = not $ propMatch trueVars p

prop_noFloatingBits (problem::Problem Var) =
    let (sat, trueProps) = solveA mode problem in
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
    solve mode [c] == bfResult
    where bfResult = solve BruteForce [c]

prop_multipleConstraints :: Property
prop_multipleConstraints = forAll multiConstraintProblem $ \p ->
    let bfResult = solve BruteForce p in
    classify (bfResult == True) "SAT" $
    classify (bfResult == False) "UNSAT" $
    solve mode (p::[Constraint Var]) == bfResult

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

--summarizeIRVElection :: [Proposition a] -> [Proposition a] -> Constraint a -> String
summarizeIRVElection trueProps allTheProps ineq =
    let print = tell . (++"\n") . show
        putStrLn = tell . (++"\n") in execWriter $ do
  let falseProps = allTheProps \\ trueProps
  let trueVoteData = map fromProposition $
                     filter (\prop -> (not . isAux) prop && (not . isSurrogate) prop) $
                     trueProps
  let votes = reconstructVotes trueVoteData
  let survivors = calculateSurvivors trueVoteData
  let surrStatus = map (\s -> (s, "1")) $ sortBy (comparing sTag) $
                   filter (not . (=~ "non-uniq") . sTag) $
                   filter isSurrogate $
                   trueProps
  let surrStatusFalse  = map (\s -> (s, "0")) $ sortBy (comparing sTag) $
                         filter (not . (=~ "non-uniq") . sTag) $
                         filter isSurrogate $
                         falseProps
  let pointStatus = filter (("point " `isPrefixOf`) . sTag) $
                    filter isSurrogate $ 
                    trueProps
  let pointStatusFalse = filter (("point " `isPrefixOf`) . sTag) $
                         filter isSurrogate $
                         falseProps
  putStrLn "Votes:"
  mapM_ print votes
  putStrLn "Survivors at the beginning of each round:"
  mapM_ print survivors
  putStrLn "Surrogate info:"
  mapM_ (\(a,b) -> putStrLn $ a ++ " " ++ b) $ map ((second show) . flop) $ (mergeBy (sTag . fst) surrStatus surrStatusFalse)
  putStrLn "Point info:"
  mapM_ print pointStatus
      
  --Print all the unique ineqNumbers used in the reduction of this problem
  --print $ sortNub $ map auxIneqNumber $ filter isAux $ trueProps ++ falseProps
        
  putStrLn ""
  
  let trueProps' = filter (\p -> isAux p && auxIneqNumber p == 1003001000) trueProps
  mapM_ print trueProps'
  mapM_ putStrLn $ map (\(a, b) -> b ++ " " ++ concat (intersperse "," a)) $ assignmentInterpretation trueProps' ineq
reconstructVotes tvd = [map vdCandidate $
                        sortBy (comparing vdPosition) $
                        filter (\vd -> vdVoter vd == v) $
                        filter isVoteDatum $
                        tvd | v <- voters]
    where voters = [1..maximum (map vdVoter $ filter isVoteDatum tvd)]
calculateSurvivors tvd = [filter (not . (isEliminated r)) candidates | r <- [0..length candidates - 1]]
    where candidates = nub $ map vdCandidate $ filter isVoteDatum tvd
          isEliminated r c = not $ null $
                             filter (\elimination -> eCandidate elimination == c && eRound elimination == r) $
                             filter isElimination tvd

prop_nestedInequalities (constraints' :: [Constraint Var]) =
    let constraints = map (\(c, i) -> fmap (\var -> (var, i)) c) (zip constraints' [0..]) in
    length constraints <= 10 ==>
    let numSatisfiable = length (filter (solve ZChaff . (:[])) constraints) in
    trace ("numSatisfiable: " ++ show numSatisfiable) $
          (--traceIt $
           solve ZChaff $
           embedConstraints (map show constraints) constraints $ \surrogates ->
               [Inequality ([(-1, surrogate) | surrogate <- surrogates], -numSatisfiable)])
          && (--traceIt $
              not $
          (solve ZChaff $
           embedConstraints (map show constraints) constraints $ \surrogates ->
               [Inequality ([(-1, surrogate) | surrogate <- surrogates], -(numSatisfiable+1))]))
                                
-- Test expressions
{-
sampleFormula = embedConstraint "sample" (trans (-10) $ Inequality ([(1, Merely 'a'),
                                              (1, Merely 'b'),
                                              (1, Merely 'c'),
                                              (1, Merely 'd'),
                                              (1, Merely 'e'),
                                              (1, Merely 'f')], 3)) $ \t ->
                embedConstraint "sample2" (Formula [Clause [Merely 'a'], Clause [Merely 'e'], Clause [Merely 'd'], Clause [Merely 'f']]) $ \fade ->
                trans (-5) $ Inequality ([(-1, t), (-1, fade)], -1)
                {-Formula [Clause [Not $ Merely $ 'b',
                                 Not $ Merely $ 'c',
                                       Merely $ 'd'],
                         Clause [      Merely 'b'],
                         Clause [Not $ Merely 'd',
                                       ae,
                                       Merely 'f'],
                         Clause [Not $ Merely 'b',
                                       Merely 'd'],
                         Clause [t]]-}
  -}             
reductionTest = embedConstraint "fake (a and b)" (Formula [Clause [Merely 'a'], Clause [Merely 'b']]) $ \fakeAandB -> [Formula [Clause [Not $ fakeAandB],
                                                                                                                                --Clause [Merely 'a'],
                                                                                                                                Clause [Merely 'b']]]

getProblem = do
  x <- e
  let problem = irvManipulation (\n -> [1,0,0,0,0,0]) (Candidate 3) 1 x
  return problem

solveWithAdditional (partial, allTheProps) problem2 = do
    let (sat, trueProps) = partial problem2
    ineqData <- readFile $ "ineqDump"++show (Candidate 3) ++ show (Candidate 1) ++ show 0
    let ineq = read ineqData :: Constraint (VoteDatum Int)
    if not sat then
        return "UNSAT"
     else
        return $ summarizeIRVElection trueProps allTheProps ineq

getPartial = do
  problem <- getProblem
  let partial = startPartial ZChaff problem
  let (sat, trueProps) = partial []
  let allTheProps = allProps problem

  --let ineq = Inequality ([],0) :: Constraint (VoteDatum Int) --read ineqData :: Constraint (VoteDatum Int)
  ineqData <- readFile $ "ineqDump"++show (Candidate 3) ++ show (Candidate 1) ++ show 0
  let ineq = read ineqData :: Constraint (VoteDatum Int)
  let summary = summarizeIRVElection trueProps allTheProps ineq
  if not sat then
        return ((partial, allTheProps), "UNSAT")
     else
        return ((partial, allTheProps), summary)

--partial <- setup
main = do
  (p, s) <- getPartial
  getProblem >>= (writeFile "theProblem") . show
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