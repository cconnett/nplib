module Utilities where

import Data.List
import Control.Monad
import Control.Parallel
import qualified Data.Set as S
import qualified Data.Map as M
import Debug.Trace
import Test.QuickCheck

traceIt s = trace ("\nTRACEIT:" ++ show s) s

-- nub with an upper limit
nub' :: Eq a => Int -> [a] -> [a]
nub' n list
    | length currentSet == min (length list) n = currentSet
    | otherwise = nub' n $ currentSet ++ (drop n list)
    where currentSet = nub $ take n list

prop_nub'_nub list = nub list == nub' (length list) list
prop_nub'_subset list = length list >= 3 ==> S.fromList (nub' 3 list) `S.isSubsetOf` S.fromList list
            
-- Find the first item in the given search space that satisfies the
-- predicate p, by unbounded binary search.  Search space may be
-- infinite.  The predicate must be unsatisfiable up to some point in
-- the search space, after which all elements satisfy it.  This
-- function is intended to be used when computing the predicate is
-- expensive.
findFast :: MonadPlus m => (a -> Bool) -> [a] -> m a
findFast p space = liftM (space !!) answer
    where answer = findFast' (map p space) 0
findFast' cache step
    | null cache = mzero
    | head cache = return 0
    | (not $ cache `hasIndex` point) || cache !! point =
        liftM (ps +) $ findFast' (drop ps cache) 0
    | otherwise = findFast' cache (next step)
    where point = step
          ps = prev step

next 0 = 1
next s = 2*s
prev 1 = 1
prev s = s `div` 2
         
hasIndex [] c = False
hasIndex list 0 = True
hasIndex list c = (tail list) `hasIndex` (c-1)

prop_FindFastFinitePresent target list = any (>target) list ==>
    ((fromJust $ findFast (>target) (sort list)) ==
     (head $ dropWhile (<=target) (sort list)))

prop_FindFastFiniteAbsent target list =
    all (<=target) list ==> ((findFast (>target) (sort list)) == Nothing)

prop_FindFastInfinite target starting = it == Just starting || it == Just (target + 1)
    where it = findFast (>target) [starting..]

               
circularZip :: [[a]] -> [a]
circularZip [] = []
circularZip lists = concat [concatMap (take 1) lists,
                            circularZip $ filter (not . null) $ map (drop 1) lists]

parfilter p [] = []
parfilter p (x:xs) =
    let ans = p x
        rest = parfilter p xs
    in (ans `par` rest) `seq` if ans then (x:rest) else rest

merge :: Ord a => [a] -> [a] -> [a]
merge = mergeBy id

mergeBy :: Ord b => (a -> b) -> [a] -> [a] -> [a]
mergeBy f as [] = as
mergeBy f [] bs = bs
mergeBy f (a:as) (b:bs)
    | f a <= f b = a:(mergeBy f as (b:bs))
    | otherwise = b:(mergeBy f (a:as) bs)

sortNub = S.toList . S.fromList
