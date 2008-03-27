module Main where

import Voting
import Elections
import System
import Test.QuickCheck
import RunGenIO
import Random
import Control.Monad

main = do
  setStdGen $ mkStdGen 19019
  args <- getArgs
  if length args /= 4
    then error "GenElections count distribution candidates nonmanipulators"
    else do
      let count = (read $ args !! 0) :: Int
          candidates = map Candidate [1..read $ args !! 2]
          nonmanipulators = (read $ args !! 3) :: Int
      voteGenerator <- runGenIO $ getVoteGenerator (words $ args !! 1) candidates
      elections <- runGenIO $ replicateM count $
                   election voteGenerator nonmanipulators
      putStrLn $ show $ elections
