{-# OPTIONS -fno-cse #-}

module SatSolvers
    (solveAll
     ,parse
     ,SatSolver(ZChaff,RSat,Minisat,Clasp)
     ,Model
     ,SolverComments
    )
    where

import SAT

import Control.Arrow
import Control.Monad
import Data.List
import Data.Maybe
import Foreign (unsafePerformIO)
import System.Cmd
import System.Directory
import System.Exit
import System.IO
import System.Process
import Test.QuickCheck
import Text.Regex.PCRE
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Set as S

import Tracing

solversHome = "./sat/"

type Model = IM.IntMap Bool
type SolverComments = [(String, String)]

-- Solve a formula, and return (the satisfiability status, Maybe list
-- of Models containing the truth assignments of the variables,
-- miscellaneous implementation specific comments from the solver
-- about the solve that produced each model).

{-# NOINLINE solveAll #-}
solveAll :: SatSolver -> (Int, Formula) -> (Maybe Bool, [Model], [SolverComments])
solveAll ss (numVars, formula) = unsafePerformIO $ runAll ss (numVars, formula)

data SatSolver = ZChaff | RSat | Minisat | Clasp
                 deriving (Show)
instance Arbitrary SatSolver where
    arbitrary = elements [ZChaff, RSat, Minisat, Clasp]
    coarbitrary = undefined

run1 :: SatSolver -> String -> IO (String, String)
--run1 ZChaff = zchaffRun1
--run1 RSat = rsatRun1
--run1 Minisat = minisatRun1
run1 Clasp = claspRun1

parse :: SatSolver -> (String, String) -> (Maybe Bool, Maybe Model, SolverComments)
--parse ZChaff = zchaffParse
--parse RSat = rsatParse
--parse Minisat = minisatParse
parse Clasp = claspParse

runAll :: SatSolver -> (Int, Formula) -> IO (Maybe Bool, [Model], [SolverComments])
runAll ss (numVars, formula) = do
  solutions <- runAll' ss (numVars, formula)
  return $ case solutions of
             (Just False, _, comments) : _ -> (Just False, [], [comments])
             (Nothing   , _, comments) : _ -> (Nothing, [], [comments])
             (Just True , _, comments) : _ -> (Just True,
                                              catMaybes $ map (\(s,m,c) -> m) solutions,
                                              map (\(s,m,c) -> c) solutions)

runAll' :: SatSolver -> (Int, Formula) -> IO [(Maybe Bool, Maybe Model, SolverComments)]
runAll' ss (numVars, formula) = do
  firstOutput <- myTrace 1 (show numVars ++ " variables, " ++
                            show (SAT.numClauses formula) ++ " clauses.\n") $
                          run1 ss (toDIMACS (numVars, formula))
  let firstSolution = parse ss firstOutput
  let restSolutions = runAll' ss (numVars, conjoin formula (invalidateModel $ (\(s,Just m,c) -> m) firstSolution))
  return $ firstSolution : (unsafePerformIO restSolutions)

invalidateModel :: Model -> Formula
invalidateModel model = fromListForm
 [[if assignedTrue then
       Not var else
       Merely var
   | (var, assignedTrue) <- IM.toList model]]

zchaffRun1 dimacs = do
  (tmpname, handle) <- openTempFile "/tmp/" "sat.cnf"
  hPutStr handle dimacs
  hClose handle
  (inp, result, err, satProcess) <-
      runInteractiveProcess (solversHome ++ "zchaff64/zchaff")
                   [tmpname]
                   Nothing Nothing
  hClose inp
  hClose err
  readResult <- hGetContents result
  putStr $ filter (const False) readResult
  hClose result
  --getProcessExitCode satProcess
  waitForProcess satProcess
  removeFile tmpname
  return (readResult, "")

-- Parse the output of zchaff into answers about the formula.
zchaffParse :: (String, String) -> (Maybe Bool, Model)
zchaffParse (stdout, assignmentFile) =
    let assignmentLine = (lines stdout) !! 5
        assignmentStrings = words assignmentLine
        assignments = map read (take (length assignmentStrings - 4) $ assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
    in case stdout of
         _ | stdout =~ "UNSAT" -> (Just False, undefined)
         _ | stdout =~ "SAT" -> (Just True, IM.fromList $
                                         [(var, True) | var <- trues] ++
                                         [(var, False) | var <- falses])
         _ | otherwise -> (Nothing, undefined)

rsatRun1 dimacs = do
  (dimacsName, handle) <- openTempFile "/tmp/" "sat.cnf"
  hPutStr handle dimacs
  hClose handle
  (inp, result, err, satProcess) <-
      runInteractiveProcess "/bin/bash"
                    ["rsat.sh", dimacsName]
                    (Just $ solversHome ++ "rsat_SAT-Race08_final_bin/") Nothing
  hClose inp
  hClose err
  readResult <- hGetContents result
  putStr $ filter (const False) readResult
  hClose result
  getProcessExitCode satProcess
  waitForProcess satProcess
  removeFile dimacsName
  return (readResult, "")

-- Parse the output of rsat into answers about the formula.
rsatParse :: (String, String) -> (Maybe Bool, Model)
rsatParse (stdout, assignmentFile) =
    let assignmentLine = last $ lines stdout
        assignmentStrings = tail $ words assignmentLine
        assignment = map read (init assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignment
        sat = case stdout of
                _ | stdout =~ "UNSATISFIABLE" -> Just False
                _ | stdout =~ "SATISFIABLE" -> Just True
                _ | otherwise -> Nothing
    in (sat, case sat of
               Just True -> IM.fromList $
                           [(var, True) | var <- trues] ++
                           [(var, False) | var <- falses]
               _ -> error "No solution")

minisatRun1 dimacs = do
  (dimacsName, handle) <- openTempFile "/tmp/" "sat.cnf"
  hPutStr handle dimacs
  hClose handle
  (stdoutName, handle2) <- openTempFile "/tmp/" "minisat.stdout"
  hClose handle2
  (solutionName, handle3) <- openTempFile "/tmp/" "minisat.sol"
  hClose handle3
  minisatRealRun dimacsName stdoutName solutionName
  readAnswer <- readFile stdoutName
  readSolution <- readFile solutionName
  putStr (filter (const False) readAnswer)
  removeFile dimacsName
  removeFile stdoutName
  removeFile solutionName
  return (readAnswer, readSolution)

minisatRealRun dimacsName stdoutName solutionName = do
  let cmd = "bash -c 'ulimit -t 60; " ++
                   solversHome ++ "minisat/simp/minisat " ++
                   dimacsName ++ " " ++
                   solutionName ++ " " ++
                   "2> /dev/null 1> " ++ stdoutName ++
                   "'"
  status <- system cmd
  case status of
    ExitSuccess -> return ()
    ExitFailure n -> if n `elem` [2,10,20,158] then
                        return () else
                        error ("Minisat failure: " ++ show status)

-- Parse the output of minisat into answers about the formula.
minisatParse :: (String, String) -> (Maybe Bool, Model)
minisatParse (stdout, assignmentFile) =
    let assignmentLine = (lines assignmentFile) !! 1
        assignmentStrings = words assignmentLine
        assignments = map read (init assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
        sat = case stdout of
                _ | stdout =~ "UNSATISFIABLE" -> Just False
                _ | stdout =~ "SATISFIABLE" -> Just True
                _ | otherwise -> Nothing
    in (sat, case sat of
               Just True -> IM.fromList $
                           [(var, True) | var <- trues] ++
                           [(var, False) | var <- falses]
               _ -> error "No solution")

claspRun1 dimacs = do
  (dimacsName, handle) <- openTempFile "/tmp/" "sat.cnf"
  hPutStr handle dimacs
  hClose handle
  (stdoutName, handle2) <- openTempFile "/tmp/" "clasp.stdout"
  hClose handle2
  claspRealRun dimacsName stdoutName
  readAnswer <- readFile stdoutName
  putStr (filter (const False) readAnswer)
  removeFile dimacsName
  removeFile stdoutName
  return (readAnswer, "")

claspRealRun dimacsName stdoutName = do
  let cmd = "bash -c 'ulimit -t 60; " ++
                   solversHome ++ "clasp/bin/clasp --dimacs --stats < " ++
                   dimacsName ++ " " ++
                   "2> /dev/null 1> " ++ stdoutName ++
                   "'"
  status <- system cmd
  case status of
    ExitSuccess -> return ()
    ExitFailure n -> if n `elem` [2,10,20] then
                        return () else
                        error ("Clasp failure: " ++ show status)

-- Parse the output of clasp into answers about the formula.
claspParse :: (String, String) -> (Maybe Bool, Maybe Model, SolverComments)
claspParse (stdout, assignmentFile) =
    let assignmentLines = filter ((=="v") . take 1) (lines stdout)
        assignmentStrings = concatMap (tail . words) assignmentLines
        assignments = map read assignmentStrings
        comments = filter (\(_,_,_,groups) -> length groups == 2) $ (map (=~"c (.*?)\\s*: (.*)") (lines stdout) :: [(String, String, String, [String])])
        commentAssoc = map (\ (_,_,_,[k, a]) -> (k, a)) comments
        (trues, falses) = second (map abs) $ partition (>0) assignments
        sat = case stdout of
                _ | stdout =~ "UNSATISFIABLE" -> Just False
                _ | stdout =~ "SATISFIABLE" -> Just True
                _ | otherwise -> Nothing
    in (sat, case sat of
               Just True -> Just $ IM.fromList $
                           [(var, True) | var <- trues] ++
                           [(var, False) | var <- falses]
               _ -> Nothing,
               commentAssoc
       )
