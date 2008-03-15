{-# OPTIONS -fno-cse #-}

module ZChaffSolver where

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

import Debug.Trace
import Utilities
    
data ZChaff = ZChaff
instance Solver ZChaff where
    startPartial s = zchaffA

-- Conversion of Problem instances to DIMACS (CNF-SAT) formats.
toDIMACS varMap (Formula clauses) = toDIMACS' varMap clauses
toDIMACS varMap (TopFormula clauses) = toDIMACS' varMap clauses
toDIMACS' varMap clauses = --trace (show clauses) $
     [map transformProposition $ fromClause clause
          | clause <- clauses]
        where transformProposition (Not p) = -(transformProposition p)
              transformProposition p = (varMap M.! p)

-- Runs a SAT constraint through zchaff and returns zchaff's answer
-- regarding satisfiability, plus a list of the variables assigned a
-- truth value of true.

{-# NOINLINE zchaffA #-}
zchaffA :: (Show a, Ord a, Read b, Integral b) =>
           ([[b]], VarMap a b) -> Problem a -> (Bool, [Proposition a])
zchaffA (cnf1, varMap1) =
  let closure problem2 =
          let formula2 = conjoin $ toSAT (detrivialize problem2)
              varMapUnion = extendVarMap varMap1 (fromFormula formula2)
              cnf2 = toDIMACS varMapUnion formula2
              numVars = M.size varMapUnion
              numClauses = length cnf1 + length cnf2
              dimacs = unlines $
                  ("p cnf " ++ trace (show numVars) (show numVars) ++ " " ++
                               trace (show numClauses) (show numClauses)) :
                  (map (unwords . (map show) . (++[0])) $ cnf1 ++ cnf2)
          in
          unsafePerformIO $ do
            (tmpname, handle) <- openTempFile "/tmp/" "zchaff.cnf"
            hPutStr handle dimacs
            hClose handle
            (inp, result, err, zchaffProcess) <-
                runInteractiveProcess "/home/chris/schoolwork/thesis/sat/zchaff64/zchaff"
                                      [tmpname]
                                      Nothing Nothing
            hClose inp
            hClose err
            readResult <- hGetContents result
            putStr (filter (\x -> False) readResult)
            hClose result
            --getProcessExitCode zchaffProcess
            waitForProcess zchaffProcess
            removeFile tmpname
            return $ zchaffParse varMapUnion readResult
  in closure

-- Parse the output of zchaff into answers about the formula.
zchaffParse :: (Ord a, Read b, Integral b) => VarMap a b -> String -> (Bool, [Proposition a])
zchaffParse varMapF answer =
    let assignmentLine = (lines answer) !! 5
        answerLine = last $ lines answer
        assignmentStrings = words assignmentLine
        assignments = map read (take (length assignmentStrings - 4) $ assignmentStrings)
        varMapR = M.fromList $ map (\(a,b)->(b,a)) $
                  M.toList $ varMapF
    in (not $ answer =~ "UNSAT",
        mapMaybe ((flip M.lookup) varMapR) $ filter (>0) assignments)
