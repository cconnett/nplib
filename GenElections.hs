module Main where

import Voting
import Elections
import System
import Test.QuickCheck
import RunGenIO
import Random
    
prop_genElections distribution candidates nonmanipulators =
    forAll (election distribution (map Candidate [1..candidates]) nonmanipulators)
               (\e -> True)
        
main = do
  setStdGen $ mkStdGen 19019
  args <- getArgs
  if length args /= 4
    then error "Elections count distribution candidates nonmanipulators"
    else
        do
          let count = (read $ args !! 0) :: Int
              voteGenerator = (read $ args !! 1) :: VoteGenerator Int
              candidates = (read $ args !! 2) :: Int
              nonmanipulators = (read $ args !! 3) :: Int
          elections <- runGenIO $ sequence $ replicate count $
                         election
                           voteGenerator
                           (map Candidate [1..candidates])
                           nonmanipulators
          putStrLn $ show $ elections
