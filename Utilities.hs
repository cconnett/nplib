{-# OPTIONS -fglasgow-exts -fno-monomorphism-restriction #-}

module Utilities where

import Maybe
import Data.List
import Control.Monad
import Control.Parallel
import qualified Data.Set as S
import qualified Data.Map as M
import Debug.Trace
import Test.QuickCheck
import Foreign (unsafePerformIO)

debug = True
myTrace = if debug then trace else flip const
traceIt s = myTrace ("\nTRACEIT:" ++ show s) s

-- nub with an upper limit
nub' :: Eq a => Int -> [a] -> [a]
nub' n list
    | length currentSet == min (length list) n = currentSet
    | otherwise = nub' n $ currentSet ++ (drop n list)
    where currentSet = nub $ take n list

prop_nub'_nub list = nub list == nub' (length list) list
prop_nub'_subset list = length list >= 3 ==> S.fromList (nub' 3 list) `S.isSubsetOf` S.fromList list

filter3 pred3 [] = ([], [])
filter3 pred3 (a:as) =
    case pred3 a of
      Nothing -> (y,a:m)
      Just True -> (a:y,m)
      Just False -> (y,m)
    where (y,m) = filter3 pred3 as

-- Find the first item in the given search space that satisfies the
-- predicate p, by unbounded binary search.  Search space may be
-- infinite.  The predicate must be unsatisfiable up to some point in
-- the search space, after which all elements satisfy it.  This
-- function is intended to be used when computing the predicate is
-- expensive.
findFirst :: MonadPlus m => (a -> Bool) -> [a] -> m a
findFirst p space = liftM (space !!) answer
    where answer = findFirst' (map p space) 0
findFirst' cache step
    | null cache = mzero
    | head cache = return 0
    | (not $ cache `hasIndex` point) || cache !! point =
        liftM (ps +) $ findFirst' (drop ps cache) 0
    | otherwise = findFirst' cache (next step)
    where point = step
          ps = prev step

next 0 = 1
next s = 2*s
prev 1 = 1
prev s = s `div` 2
         
hasIndex [] c = False
hasIndex list 0 = True
hasIndex list c = (tail list) `hasIndex` (c-1)

prop_FindFirstFinitePresent target list = any (>target) list ==>
    ((fromJust $ findFirst (>target) (sort list)) ==
     (head $ dropWhile (<=target) (sort list)))

prop_FindFirstFiniteAbsent target list =
    all (<=target) list ==> ((findFirst (>target) (sort list)) == Nothing)

prop_FindFirstInfinite target starting = it == Just starting || it == Just (target + 1)
    where it = findFirst (>target) [starting..]

               
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

permCache filename thunk =
    unsafePerformIO $ do
      result <- catch
                ((liftM read) $ readFile filename)
                (\e -> do
                   writeFile filename (show thunk)
                   return thunk)
      return result
