{-# OPTIONS -fno-cse #-}

module SatSolvers where

import VarMapping
import ILPSAT
import ILPSATReduction
import Solvers

import Text.Regex.Posix
import Data.Maybe
import System.IO
import System.Directory
import System.Process
import qualified Data.Map as M
import qualified Data.Set as S
import Foreign (unsafePerformIO)

import Utilities

solversHome = "/home/chris/schoolwork/thesis/sat/"

class SatSolver ss where
    run :: ss -> String -> IO String
    parse :: (Ord a, Read b, Integral b) =>
             ss -> VarMap a b -> String -> (Maybe Bool, [Proposition a])

data ZChaff = ZChaff
instance Solver ZChaff where
    startPartial s = satA s
instance SatSolver ZChaff where
    run ss = zchaffRun
    parse ss = zchaffParse

data RSat = RSat
instance Solver RSat where
    startPartial s = satA s
instance SatSolver RSat where
    run ss = rsatRun
    parse ss = rsatParse

-- Conversion of Problem instances to DIMACS (CNF-SAT) formats.
toDIMACS varMap (Formula clauses) = toDIMACS' varMap clauses
toDIMACS varMap (TopFormula clauses) = toDIMACS' varMap clauses
toDIMACS' varMap clauses =
     [map transformProposition $ fromClause clause
          | clause <- clauses]
        where transformProposition (Not p) = -(transformProposition p)
              transformProposition p = (varMap M.! p)

-- Runs a SAT constraint through a sat solver and returns its answer
-- regarding satisfiability, plus a list of the variables assigned a
-- truth value of true.

{-# NOINLINE satA #-}
satA :: (SatSolver ss, Show a, Ord a, Read b, Integral b) =>
        ss -> ([[b]], VarMap a b) -> Problem a -> (Maybe Bool, [Proposition a])
satA ss (cnf1, varMap1) =
  let closure problem2 =
          let formula2 = conjoin $ toSAT (detrivialize problem2)
              varMapUnion = extendVarMap varMap1 (fromFormula formula2)
              cnf2 = toDIMACS varMapUnion formula2
              numVars = M.size varMapUnion
              numClauses = length cnf1 + length cnf2
              dimacs = unlines $
                  ("p cnf " ++ myTrace (show numVars) (show numVars) ++ " " ++
                               myTrace (show numClauses) (show numClauses)) :
                  (map (unwords . (map show) . (++[0])) $ cnf1 ++ cnf2)
          in
          let readResult = unsafePerformIO $ run ss dimacs in
          parse ss varMapUnion readResult
  in closure

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
  print (filter (\x -> True) readResult)
  hClose result
  --getProcessExitCode satProcess
  waitForProcess satProcess
  removeFile tmpname
  return readResult

-- Parse the output of zchaff into answers about the formula.
zchaffParse :: (Ord a, Read b, Integral b) => VarMap a b -> String -> (Maybe Bool, [Proposition a])
zchaffParse varMapF answer =
    let assignmentLine = (lines answer) !! 5
        answerLine = last $ lines answer
        assignmentStrings = words assignmentLine
        assignments = map read (take (length assignmentStrings - 4) $ assignmentStrings)
        varMapR = M.fromList $ map (\(a,b)->(b,a)) $
                  M.toList $ varMapF
    in (Just $ not $ answer =~ "UNSAT",
        mapMaybe ((flip M.lookup) varMapR) $ filter (>0) assignments)

rsatRun dimacs = do
  (tmpname, handle) <- openTempFile "/tmp/" "sat.cnf"
  hPutStr handle dimacs
  hClose handle
  (inp, result, err, satProcess) <-
      runInteractiveProcess (solversHome ++ "rsat_2.01_release/rsat")
                   [tmpname, "-s", "-t", "360"]
                   Nothing Nothing
  hClose inp
  hClose err
  readResult <- hGetContents result
  putStr (filter (\x -> False) readResult)
  hClose result
  --getProcessExitCode satProcess
  waitForProcess satProcess
  removeFile tmpname
  return readResult

-- Parse the output of rsat into answers about the formula.
rsatParse :: (Ord a, Read b, Integral b) => VarMap a b -> String -> (Maybe Bool, [Proposition a])
rsatParse varMapF answer =
    let assignmentLine = (lines answer) !! 2
        answerLine = last $ lines answer
        assignmentStrings = words assignmentLine
        assignments = map read (init assignmentStrings)
        varMapR = M.fromList $ map (\(a,b)->(b,a)) $
                  M.toList $ varMapF
    in (if answer =~ "UNKNOWN" then Nothing else Just $
        not $ answer =~ "UNSATISFIABLE",
        mapMaybe ((flip M.lookup) varMapR) $ filter (>0) assignments)
