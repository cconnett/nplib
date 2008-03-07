module RunGenIO
    where

import Test.QuickCheck
import Random
      
runGenIO :: Gen a -> IO a
runGenIO gen = do
  r <- getStdGen
  seed <- randomRIO (0, 50)
  return $ generate seed r gen
