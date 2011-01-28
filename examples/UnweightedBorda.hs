module Main where

import SatSolvers
import NPLib
import NInteger
import Control.Monad
import Data.Array

--unweightedBorda :: Integer -> Integer -> [Integer] -> InstanceBuilder ()
unweightedBorda m startingScores = do
  let r = fromIntegral $ length startingScores
  x <- liftM (listArray ((0,2,2),(m,r,r))) $ takeSatVars $ fromIntegral $ (m+1) * (r-1) * (r-1)
  forM_ [2..r] $ \i2 -> do
    forM_ [2..r] $ \i3 -> do
      s <- nsum [x ! (i1, i2, i3) | i1 <- [0..m]]
      s `equal` (NInteger.fromInteger 1) >>= assert
  forM_ [2..r] $ \i2 -> do
    ixTerms <- sequence [sequence [mul1bit (NInteger.fromInteger i1 :: NInteger) (x ! (i1, i2, i3)) | i3 <- [2..r]] | i1 <- [0..m]]
    s <- nsum $ concat ixTerms
    (s :: NInteger) `equal` (NInteger.fromInteger m) >>= assert
    --ntrace ("ixTerms " ++ show i2) ixTerms (show :: [[Integer]] -> String)
    scoreTerms <- sequence [sequence [mul (NInteger.fromInteger (r - i3)) ixTerm | (i3, ixTerm) <- zip [2..r] ixSubTerms] | (i1, ixSubTerms) <- zip [0..m] ixTerms]
    --ntrace ("scoreTerms " ++ show i2) scoreTerms (show :: [[Integer]] -> String)
    manipulationScore <- nsum $ concat scoreTerms
    manipulationScore `leq` (NInteger.fromInteger $ head startingScores + m * (r - 1) - startingScores !! fromIntegral (i2 - 1)) >>= assert
    --ntrace ("score " ++ show i2) manipulationScore (show :: Integer -> String)
  forM_ [2..r] $ \i3 -> do
    s <- nsum =<< sequence [mul1bit (NInteger.fromInteger i1 :: NInteger) (x ! (i1, i2, i3)) | i1 <- [0..m], i2 <- [2..r]]
    (s :: NInteger) `equal` (NInteger.fromInteger m) >>= assert
  return x

main = do
  let m = 2
  let scores = [0,5,5,5,9,9,9]
  let r = fromIntegral $ length scores
  let (result, x) = evalInstance Clasp (unweightedBorda m scores) :: (Maybe Bool, Array (Integer, Integer, Integer) Bool)
  print result
  --forM_ (range ((0,2,2),(m,r,r))) $ \(i1,i2,i3) -> when (x ! (i1,i2,i3)) (putStrLn (show i1 ++ " manipulators put " ++ show i2 ++ " in position " ++ show i3))
  return ()