module VarMapping where

import Data.List
import qualified Data.Set as S
import qualified Data.Map as M
import ILPSAT
import ILPSATReduction
import Utilities

varMap formula = M.fromDistinctAscList $ zip (allVars (Formula formula)) [1..]
extendVarMap mp clauses = mkMap' mp (concatMap fromClause clauses)

mkMap items = mkMap' (M.empty) items
mkMap' mp [] = mp
mkMap' mp (item:items) = let nextIndex = M.size mp + 1 in
                         mkMap' (M.insertWith (flip const) item nextIndex mp) items
prop_mkMapAllKeys (items :: [Int]) =
    let mp = mkMap items in
    all (flip M.member mp) items

allVars :: (Ord a, Eq a) => Constraint a -> [Proposition a]
allVars = (S.toList) . varSet
varSet :: (Ord a, Eq a) => Constraint a -> S.Set (Proposition a)
varSet (Formula formula) = --trace "varSet called" $
    let x = (S.fromList $ map normalizeProposition $
             concatMap fromClause $ formula)
    in x --seq x (trace "varSet evaluated" x)
varSet (TopFormula formula) =
    S.fromList $
     map normalizeProposition $
     concatMap fromClause $ formula
varSet (Inequality ineq) = S.fromList $ map snd $ fst ineq
varSubsets i@(Inequality ineq) = sortNub $ map auxVarSet $ filter isAux $ (allVars (conjoin $ toSAT [i]))
