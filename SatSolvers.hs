{-# OPTIONS -fno-cse #-}

module SatSolvers where

import SAT

import Text.Regex.Posix
import Control.Monad
import Control.Arrow
import Data.Maybe
import Data.List
import System.IO
import System.Directory
import System.Process
import System.Cmd
import System.Exit
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Set as S
import Foreign (unsafePerformIO)

import Utilities

--solversHome = "/home/stu2/s1/cxc0117/thesis/sat.x86/"
solversHome = "/home/chris/schoolwork/thesis/sat/"

-- Solve a formula, and return a Maybe list of IntMaps containing the
-- truth assignments of the variables.  If the formula had no
-- solutions, Just [] is returned.  If the *first* solution timed out,
-- Nothing is returned.  Otherwise, (Just) a list of the non-timed out
-- solutions is returned.

{-# NOINLINE solveAll #-}
solveAll :: SatSolver -> (Int, Formula) -> Maybe [IM.IntMap Bool]
solveAll ss (numVars, formula) = unsafePerformIO $ run ss (numVars, formula)

solveA :: SatSolver -> (Int, Formula) -> (Maybe Bool, IM.IntMap Bool)
solveA ss (numVars, formula) =
    case solveAll ss (numVars, formula) of
      Nothing -> (Nothing, error "Solve time limit exceeded")
      Just [] -> (Just False, error "Unsatisfiable formula")
      Just (firstTruthMap:_) -> (Just True, firstTruthMap)

-- Solve a problem and return its satisfiablility.
solve :: SatSolver -> (Int, Formula) -> Maybe Bool
solve s problem = fst (solveA s problem)

data SatSolver = ZChaff | RSat | Minisat

-- Conversion of Problem instances to DIMACS (CNF-SAT) formats.
toDIMACS :: (Int, Formula) -> String
toDIMACS (numVars, formula) =
    let cnf = toCNF formula
        numClauses = length $ fromFormula formula
    in ("p cnf " ++
        (show numVars) ++ " " ++
        (show numClauses) ++ "\n") ++
       (unlines $ map (unwords . (map show) . (++[0])) cnf)

toCNF :: Formula -> [[Int]]
toCNF (Formula clauses) = [map transformProposition $ fromClause clause
                     | clause <- clauses]
        where transformProposition p =
                  (if isNeg p then negate else id) $ propositionVar p

run :: SatSolver -> (Int, Formula) -> IO (Maybe [IM.IntMap Bool])
run ZChaff = zchaffRun
run RSat = rsatRun
run Minisat = minisatRunAll

-- Runs a SAT constraint through a sat solver and returns its answer
-- regarding satisfiability, plus a list of the variables assigned a
-- truth value of true.

zchaffRun (numVars, formula) = do
  let dimacs = toDIMACS (numVars, formula)
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
  return $ zchaffParse readResult

-- Parse the output of zchaff into answers about the formula.
zchaffParse :: String -> Maybe [IM.IntMap Bool]
zchaffParse answer =
    let assignmentLine = (lines answer) !! 5
        answerLine = last $ lines answer
        assignmentStrings = words assignmentLine
        assignments = map read (take (length assignmentStrings - 4) $ assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
    in case answer of
         _ | answer =~ "UNSAT" -> Just []
         _ | answer =~ "SAT" -> Just $ [IM.fromList $
                                       [(var, True) | var <- trues] ++
                                       [(var, False) | var <- falses]]
         _ | otherwise -> Nothing

rsatRun (numVars, formula) = do
  let dimacs = toDIMACS (numVars, formula)
  (dimacsName, handle) <- openTempFile "/tmp/" "sat.cnf"
  hPutStr handle dimacs
  hClose handle
  (inp, result, err, satProcess) <-
      runInteractiveProcess (solversHome ++ "rsat_2.01_release/rsat")
                   [dimacsName, "-s", "-t", "60"]
                   Nothing Nothing
  hClose inp
  hClose err
  readResult <- hGetContents result
  putStr $ filter (const False) readResult
  hClose result
  --getProcessExitCode satProcess
  waitForProcess satProcess
  --removeFile dimacsName
  return $ rsatParse readResult

-- Parse the output of rsat into answers about the formula.
rsatParse :: String -> Maybe [IM.IntMap Bool]
rsatParse answer =
    let assignmentLine = (lines answer) !! 2
        assignmentStrings = tail $ words assignmentLine
        assignments = map read (init assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
    in case answer of
         _ | answer =~ "UNSATISFIABLE" -> Just []
         _ | answer =~ "SATISFIABLE" -> Just $ [IM.fromList $
                                               [(var, True) | var <- trues] ++
                                               [(var, False) | var <- falses]]
         _ | otherwise -> Nothing

minisatRunAll (numVars, formula) = do
  solutions <- minisatRunAll' (numVars, formula)
  return $ case solutions of
             (Just False, _) : _ -> Just []
             (Nothing, _) : _ -> Nothing
             (Just True, _) : _ -> Just $ map snd $ takeWhile ((==Just True) . fst) solutions

minisatRunAll' (numVars, formula) = do
  (aResult, aSolution) <- myTrace (show numVars ++ " variables, " ++
                                  show (length $ fromFormula formula) ++ " clauses.\n") $
                          minisatRun1 (toDIMACS (numVars, formula))
  let firstElement = minisatParse aResult aSolution
  let restElements = minisatRunAll' (numVars, conjoin [formula, minisatInvalidateSolution aSolution])
  return $ firstElement : (unsafePerformIO restElements)

minisatInvalidateSolution solution =
    let assignmentLine = (lines solution) !! 1
        assignmentStrings = words assignmentLine
        assignments = map read (init assignmentStrings)
    in
      Formula [Clause (map (\assignment -> if assignment < 0 then
                                              Merely (abs assignment) else
                                              Not (abs assignment))
                       assignments)]

minisatRun1 dimacs = do
  (dimacsName, handle) <- openTempFile "/tmp/" "sat.cnf"
  hPutStr handle dimacs
  hClose handle
  (stdoutName, handle2) <- openTempFile "/tmp/" "minisat.stdout"
  hClose handle2
  (solutionName, handle3) <- openTempFile "/tmp/" "minisat.sol"
  hClose handle3
  minisatRealRun dimacsName stdoutName solutionName
  readResult <- readFile stdoutName
  readSolution <- readFile solutionName
  putStr (filter (const False) readResult)
  removeFile dimacsName
  removeFile stdoutName
  removeFile solutionName
  return (readResult, readSolution)

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
    ExitFailure 10 -> return ()
    ExitFailure 20 -> return ()
    ExitFailure 158 -> return ()
    _ -> error "Minisat failure" --minisatRealRun dimacsName stdoutName solutionName
         
-- Parse the output of minisat into answers about the formula.
minisatParse :: String -> String -> (Maybe Bool, IM.IntMap Bool)
minisatParse answer solution =
    let assignmentLine = (lines solution) !! 1
        assignmentStrings = words assignmentLine
        assignments = map read (init assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
        sat = case answer of
                _ | answer =~ "UNSATISFIABLE" -> Just False
                _ | answer =~ "SATISFIABLE" -> Just True
                _ | otherwise -> Nothing
    in (sat, case sat of
               Just True -> IM.fromList $
                           [(var, True) | var <- trues] ++
                           [(var, False) | var <- falses]
               _ -> error "No solution")

