{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import SatSolvers
import NPLib
import NInteger
import Control.Monad
import Data.Array
import Data.Maybe
import System.Random

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
  setStdGen (mkStdGen 50)
  scores <- readLn :: IO [Int]
  m <- readLn :: IO Int
  weights <- replicateM m $ randomRIO (1, 2^m)
  let r = fromIntegral $ length scores
  let inst = buildInstance Clasp (weightedApproval (fromIntegral m) r (map fromIntegral scores) weights)
  let result = satisfiability inst
  print scores
  print m
  print weights
  print result
  putStrLn $ "Conflicts: " ++ fromJust (lookup "Conflicts" (head $ comments inst))
  return ()
