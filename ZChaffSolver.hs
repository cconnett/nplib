module ZChaffSolver where

import VarMapping
import ILPSAT
import ILPSATReduction
import Solvers

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
toDIMACS :: (Ord a) => Constraint a -> (M.Map (Proposition a) Int, String)
toDIMACS (Formula formula) =
    (varMapF,
     unlines $ ("p cnf " ++ {-trace (show numVars)-} (show numVars) ++ " " ++ {-trace (show numClauses)-} (show numClauses)) :
                 [unwords $ (map (show.transformProposition) $ fromClause clause) ++ ["0"]
                      | clause <- formula])
        where transformProposition (Not p) = -(varMapF M.! p)
              transformProposition p = (varMapF M.! p)
              varMapF = varMap formula
              numVars = M.size varMapF
              numClauses = length formula

toDIMACS2 varMapF (Formula formula) =
     unlines $ ("p cnf " ++ {-trace (show numVars)-} (show numVars) ++ " " ++ {-trace (show numClauses)-} (show numClauses)) :
                 [unwords $ (map (show.transformProposition) $ fromClause clause) ++ ["0"]
                      | clause <- formula]
        where transformProposition (Not p) = -(varMapF M.! p)
              transformProposition p = (varMapF M.! p)
              numVars = M.size varMapF
              numClauses = length formula

-- Runs a SAT constraint through zchaff and returns zchaff's answer
-- regarding satisfiability, plus a list of the variables assigned a
-- truth value of true.

{-# NOINLINE zchaffA #-}
zchaffA :: (Show a, Ord a) => Problem a -> Problem a -> (Bool, [Proposition a])
zchaffA problem1 =
  let (varMapF, dimacs) = toDIMACS $ toSAT (detrivialize problem1) in
  let closure problem2 =
          let dimacs = toDIMACS2 varMapF $ toSAT (detrivialize $ problem1 ++ problem2) in
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
            putStr (readResult `seq` "")
            --hClose result
            getProcessExitCode zchaffProcess
            --removeFile tmpname
            return $ zchaffParse varMapF readResult
  in closure

-- Parse the output of zchaff into answers about the formula.
zchaffParse :: (Ord a) => M.Map (Proposition a) Int -> String -> (Bool, [Proposition a])
zchaffParse varMapF answer =
    --trace (show $ map ((read::String->Int).last.words) $ filter ("Original" `isPrefixOf`) $ lines answer) $
    let assignmentLine = (lines answer) !! 5
        answerLine = last $ lines answer
        assignmentStrings = words assignmentLine
        assignments = map read (take (length assignmentStrings - 4) $ assignmentStrings) :: [Int]
        varMapR = M.fromList $ map (\(a,b)->(b,a)) $
                  M.toList $ varMapF
    in ("SAT" == (words answerLine) !! 1,
        mapMaybe ((flip M.lookup) varMapR) $ filter (>0) assignments)
