module Main where

import SatSolvers
import NPLib
import NInteger
import Control.Monad
import Data.Array

weightedApproval m r scores weights = do
  x <- liftM (listArray ((1,2),(m,r))) $ takeSatVars $ fromIntegral $ m * (r-1)
  forM_ [1..m] $ \i -> do
    approvals <- nsum [x ! (i, j) | j <- [2..r]]
    approvals `equal` (NInteger.fromInteger $ r `div` 2 - 1) >>= assert
  forM_ [2..r] $ \j -> do
    scoreAdded <- sequence [mul1bit (NInteger.fromInteger (weights !! fromIntegral (i-1)) :: NInteger) (x ! (i, j)) | i <- [1..m]]
    manipulationScore <- nsum scoreAdded
    manipulationScore `leq` (NInteger.fromInteger $ head scores - scores !! fromIntegral (j-1) + sum (take (fromIntegral m) weights)) >>= assert
    ntrace ("score " ++ show j) manipulationScore
  return x

main = do
  scores <- readLn
  weights <- readLn
  let m = fromIntegral $ length weights
  let r = fromIntegral $ length scores
  let result = satisfiability $ buildInstance Clasp (weightedApproval m r scores weights)
  print result
  return ()
