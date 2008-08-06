module DebugHelp where

import VarMapping
import ILPSAT
import ILPSATReduction
import Data.Bits
import Control.Arrow
import Data.Maybe
import Utilities
import Debug.Trace
import Data.List
import Solvers
import SatSolvers

allProps problem = allVars $ conjoin $ toSAT problem

assignmentInterpretation trueProps i@(Inequality ineq) =
    sort $
    --let highBit = (maximum $ map (\varSet -> highestBit varSet i) (varSubsets i)) + 1 in
    let highBit = 6 in
    map (\(varSet, (trueAuxTerms, _)) -> (map show2 varSet,
                                                      padWithTo 'x' 6 $ showBinaryNumWidth (highestBit varSet i + 1) $
                                                      (foldr (.|.) 0 (map (bit . auxBitNo) trueAuxTerms) :: Integer))) $
    --traceIt $
    map (\varSubset -> (varSubset,
                        partition (\prop -> --isAux prop &&
                                         (auxTag prop == "p") &&
                                         (show (auxVarSet prop) == show varSubset)) trueProps)) $
    --trace ("varSets::::\n" ++ show (varSubsets i)) $
    varSubsets i
highestBit varSet i@(Inequality ineq) =
    maximum $ map auxBitNo $ filter ((==varSet) . auxVarSet) $
            filter isAux $ allVars (conjoin $ toSAT [i])
showBinaryNumWidth 0 num = ""
showBinaryNumWidth width num =
    (if testBit num (width-1) then '1' else '0') : showBinaryNumWidth (width-1) num
padWithTo char len s = replicate (len - length s) char ++ s

floatingBits problem =
    let (sat, trueProps) = solveA ZChaff problem
        allTheProps = allProps problem
        falseProps = allTheProps \\ trueProps
        compound prop =
            (Formula (map (Clause . (:[])      ) (filter (not . isAux) trueProps)) :
             Formula (map (Clause . (:[]) . neg) (filter (not . isAux) falseProps)) :
             Formula [Clause [prop]] :
             [conjoin $ toSAT problem])
    in
    filter (\prop -> all (fromJust . (solve RSat)) (map compound [prop, neg prop]))
           (filter isAux allTheProps)
