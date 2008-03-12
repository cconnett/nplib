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

data ZChaff = ZChaff
instance Solver ZChaff where
    startPartial s = zchaffA

-- Conversion of Problem instances to DIMACS (CNF-SAT) formats.
toDIMACS varMap (Formula clauses) = toDIMACS' varMap clauses
toDIMACS varMap (TopFormula clauses) = toDIMACS' varMap clauses
toDIMACS' varMap clauses =
     unlines $ ("p cnf " ++ {-trace (show numVars)-} (show numVars) ++ " " ++ {-trace (show numClauses)-} (show numClauses)) :
                 [unwords $ (map (show.transformProposition) $ fromClause clause) ++ ["0"]
                      | clause <- clauses]
        where transformProposition (Not p) = -(varMap M.! p)
              transformProposition p = (varMap M.! p)
              numVars = M.size varMap
              numClauses = length clauses

-- Runs a SAT constraint through zchaff and returns zchaff's answer
-- regarding satisfiability, plus a list of the variables assigned a
-- truth value of true.

{-# NOINLINE zchaffA #-}
zchaffA :: (Show a, Ord a) => Problem a -> Problem a -> (Bool, [Proposition a])
zchaffA problem1 =
  let varMap1 = varMap $ fromFormula $ conjoin $ toSAT (detrivialize problem1) in
  let closure problem2 =
          let varMap2 = varMap $ fromFormula $ conjoin $ toSAT (detrivialize problem2)
              varMapUnion = M.map (+ M.size varMap1) (varMap2 M.\\ varMap1)
              dimacs = toDIMACS varMapUnion $ conjoin $ toSAT (detrivialize $ problem1 ++ problem2)
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
            --removeFile tmpname
            return $ zchaffParse varMap1 readResult
  in closure

-- Parse the output of zchaff into answers about the formula.
zchaffParse :: (Ord a) => M.Map (Proposition a) Int -> String -> (Bool, [Proposition a])
zchaffParse varMapF answer =
    let assignmentLine = (lines answer) !! 5
        answerLine = last $ lines answer
        assignmentStrings = words assignmentLine
        assignments = map read (take (length assignmentStrings - 4) $ assignmentStrings) :: [Int]
        varMapR = M.fromList $ map (\(a,b)->(b,a)) $
                  M.toList $ varMapF
    in (not $ answer =~ "UNSAT",
        mapMaybe ((flip M.lookup) varMapR) $ filter (>0) assignments)
