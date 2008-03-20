{-# OPTIONS -fglasgow-exts #-}

module Main
    where

import Manipulation
import ILPSAT
import ZChaffSolver
--import GLPKSolver
import System
import Voting
import Elections
import Debug.Trace
import Data.List
import Maybe
import Control.Monad
import Test.QuickCheck
import Solvers

main = do
  args <- getArgs
  if length args /= 3
     then error "Solve method rule electionsFile"
     else do
       let electionsFilename = (args !! 2) :: String
       elections <- readElections electionsFilename
       let method = args !! 0
           winnerCalculator = case method of
                                "bf"  -> possibleWinnersByBruteForce (read (args !! 1))
                                "sat" -> possibleWinnersBySolver ZChaff (read (args !! 1)) (head elections)
                                --"ilp" -> possibleWinnersBySolver GLPK (read (args !! 1))
                                _     -> error "Supported methods are \nbf\nsat"
       sequence $
          [do let theMinimumManipulators = minimumManipulators winnerCalculator election
              putStrLn $ (show electionNo) ++ ": " ++ (show theMinimumManipulators)
              --putStrLn (show $ theMinimumManipulators !! 1)
           | (electionNo, election) <- zip [1..] elections]
