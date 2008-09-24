{-# OPTIONS -fno-cse #-}

module SatSolvers where

import SAT

import Text.Regex.Posix
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

-- Solve a problem and return its satisfiablility, plus a list of
-- the variables assigned a truth value of true.
{-# NOINLINE solveA #-}
solveA :: SatSolver -> (Int, Formula) -> (Maybe Bool, IM.IntMap Bool)
solveA ss (numVars, cnf) = unsafePerformIO $ run ss (toDIMACS (numVars, cnf))

-- Solve a problem and return its satisfiablility.
solve :: SatSolver -> (Int, Formula) -> Maybe Bool
solve s problem = fst (solveA s problem)

data SatSolver = ZChaff | RSat | Minisat

-- Conversion of Problem instances to DIMACS (CNF-SAT) formats.
toDIMACS :: (Int, Formula) -> String
toDIMACS (numVars, formula) =
    let cnf = toCNF formula
        numClauses = traceIt $ length $ fromFormula formula
    in ("p cnf " ++
        (show $ traceIt numVars) ++ " " ++
        (show numClauses) ++ "\n") ++
       (unlines $ map (unwords . (map show) . (++[0])) cnf)

toCNF :: Formula -> [[Int]]
toCNF (Formula clauses) = [map transformProposition $ fromClause clause
                     | clause <- clauses]
        where transformProposition p =
                  (if isNeg p then negate else id) $ propositionVar p

run :: SatSolver -> String -> IO (Maybe Bool, IM.IntMap Bool)
run ZChaff = zchaffRun
run RSat = rsatRun
run Minisat = minisatRun

-- Runs a SAT constraint through a sat solver and returns its answer
-- regarding satisfiability, plus a list of the variables assigned a
-- truth value of true.

zchaffRun dimacs = do
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
zchaffParse :: String -> (Maybe Bool, IM.IntMap Bool)
zchaffParse answer =
    let assignmentLine = (lines answer) !! 5
        answerLine = last $ lines answer
        assignmentStrings = words assignmentLine
        assignments = map read (take (length assignmentStrings - 4) $ assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
    in (case answer of
          _ | answer =~ "UNSAT" -> Just False
          _ | answer =~ "SAT" -> Just True
          _ | otherwise -> Nothing,
        IM.fromList $
              [(var, True) | var <- trues] ++
              [(var, False) | var <- falses])

rsatRun dimacs = do
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
rsatParse :: String -> (Maybe Bool, IM.IntMap Bool)
rsatParse answer =
    let assignmentLine = (lines answer) !! 2
        assignmentStrings = tail $ words assignmentLine
        assignments = map read (init assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
        sat = case answer of
                _ | answer =~ "UNSATISFIABLE" -> Just False
                _ | answer =~ "SATISFIABLE" -> Just True
                _ | otherwise -> Nothing
    in (sat,
           IM.fromList $
                 [(var, True) | var <- trues] ++
                 [(var, False) | var <- falses])

minisatRun dimacs = do
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
  return $ minisatParse readResult readSolution

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
    let --assignmentLine = myTrace solution $ (lines solution) !! 1
        assignmentLine = (lines solution) !! 1
        assignmentStrings = words assignmentLine
        assignments = map read (init assignmentStrings)
        (trues, falses) = second (map abs) $ partition (>0) assignments
        sat = case answer of
                _ | answer =~ "UNSATISFIABLE" -> Just False
                _ | answer =~ "SATISFIABLE" -> Just True
                _ | otherwise -> Nothing
    in (sat,
           IM.fromList $
                 [(var, True) | var <- trues] ++
                 [(var, False) | var <- falses])

