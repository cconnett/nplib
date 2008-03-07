module Main
    where

import Voting
import Elections
import Manipulation
    
import System
import IO

main = do
  args <- getArgs
  if length args /= 3
    then error "BruteForce rule manipulators electionsFile"
    else
        do
          let rule = (read $ args !! 0) :: Rule Int
              manipulators = (read $ args !! 1) :: Int
          elections <- readElections (args !! 2)
          sequence $ [putStrLn $ (show electionNo) ++ ": " ++
                                 (show $ possibleWinnersByBruteForce
                                           rule manipulators election)
                      | (electionNo, election) <- zip [1..] elections]
