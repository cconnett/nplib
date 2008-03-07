module VarMapping where

import Data.List
import qualified Data.Set as S
import qualified Data.Map as M
import ILPSAT
import ILPSATReduction
import Utilities

varMap formula = M.fromAscList $ zip (allVars (Formula formula)) [1..]
allVars :: (Ord a, Eq a) => Constraint a -> [Proposition a]
allVars = (S.toList) . varSet
varSet :: (Ord a, Eq a) => Constraint a -> S.Set (Proposition a)
varSet (Formula formula) = --trace "varSet called" $
    let x = (S.fromList $ map normalizeProposition $
             concatMap fromClause $ formula)
    in x --seq x (trace "varSet evaluated" x)
varSet (Inequality ineq) = S.fromList $ map snd $ fst ineq
varSubsets i@(Inequality ineq) = sortNub $ map auxVarSet $ filter isAux $ (allVars (toSAT [i]))
