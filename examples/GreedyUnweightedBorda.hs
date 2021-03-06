module GreedyUnweightedBorda where

import Data.List
import Debug.Trace
import Utilities

greedyUnweightedBorda (c1:cn) 0 = all (c1>=) cn
greedyUnweightedBorda (c1:cn) m = greedyUnweightedBorda (c1 + (r-1) : zipWith (+) [0..r-2] (reverse $ sort cn)) (m - 1)
    where r = length cn + 1
minGreedyUnweightedBorda scores = findFirst (greedyUnweightedBorda scores) [0..]
