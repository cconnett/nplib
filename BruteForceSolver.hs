module BruteForceSolver where

import VarMapping
import ILPSAT
import Solvers

import Data.List
import Data.Maybe
import Data.Bits
import Control.Arrow
import qualified Data.Map as M
import qualified Data.Set as S

data BruteForce = BruteForce
instance Solver BruteForce where
    solveA s = bruteForceProblem
    
bruteForceProblem :: (Ord a) => Problem a -> (Bool, [Proposition a])
bruteForceProblem p
    | M.size vm == 0 && all ((>=0).snd.fromInequality) (filter isInequality problem) = (True, [])
    | null witnesses = (False, [])
    | otherwise = (True, map (vmr M.!) (trueBits $ head witnesses))
    where problem = detrivialize p
          witnesses = filter (satisfies vm problem) [0..2^(M.size vm)-1]
          vm = M.fromList $ zip (sort $ nub $ concat $ map allVars problem) [0..]
          vmr = M.fromList $ map (\(a,b) -> (b, a)) $ M.toList vm
          trueBits a = filter (testBit a) [0..M.size vm]
                
type VM a = M.Map (Proposition a) Int

satisfies :: (Ord a) => VM a -> Problem a -> Int -> Bool
satisfies varMap p sol = all ((flip (satisfies1 varMap)) sol) p

satisfies1 :: (Ord a) => VM a -> Constraint a -> Int -> Bool
satisfies1 varMap (Formula f) sol = all ((flip (satisfiesClause varMap)) sol) f
satisfies1 varMap (Inequality (lhs, rhs)) sol = (sum $ uncurry (zipWith (*)) $ unzip lhs') <= rhs
    where lhs' = map (second (fromEnum . fst . bruteForceProblem)) lhs

satisfiesClause :: (Ord a) => VM a -> Clause a -> Int -> Bool
satisfiesClause varMap (Clause []) sol = True
satisfiesClause varMap (Clause c) sol = any propTrue c
    where propTrue (Merely a) = testBit sol (varMap M.! (Merely a))
          propTrue (Not p) = not $ testBit sol (varMap M.! p)
