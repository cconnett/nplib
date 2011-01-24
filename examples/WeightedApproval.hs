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
    ntrace ("score " ++ show j) manipulationScore (show :: Integer -> String)
  return x

main = do
  let m = 3
  let scores = [0,5,5,5,9,9,9]
  let weights = [3,7,19,15,10,25,7]
  let r = fromIntegral $ length scores
  let (result, x) = evalNProgram Clasp (weightedApproval m r scores weights) :: (Maybe Bool, Array (Integer, Integer) Bool)
  print result
  --forM_ (range ((0,2,2),(m,r,r))) $ \(i1,i2,i3) -> when (x ! (i1,i2,i3)) (putStrLn (show i1 ++ " manipulators put " ++ show i2 ++ " in position " ++ show i3))
  return ()
