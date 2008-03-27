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
  if not $ length args `elem` [3,4]
     then error "Solve method rule electionsFile [startNo]"
     else do
       let electionsFilename = (args !! 2) :: String
       let startNo = if length args == 4 then (read $ args !! 3) else 1
       elections <- readElections electionsFilename
       if (not $ 0 < startNo && startNo <= length elections) then error "Bad startNo" else do
       let method = args !! 0
           winnerCalculator = case method of
                                "bf"  -> possibleWinnersByBruteForce (read (args !! 1))
                                "f2w" -> findTwoWinners (read (args !! 1))
                                "sat" -> possibleWinnersBySolver ZChaff (read (args !! 1)) (head elections)
                                --"ilp" -> possibleWinnersBySolver GLPK (read (args !! 1))
                                _     -> error "Supported methods are \nbf\nf2w\nsat"
       sequence $
          [do let theMinimumManipulators = minimumManipulators winnerCalculator election
              putStrLn $ (show electionNo) ++ ": " ++ (show theMinimumManipulators)
           | (electionNo, election) <- zip [startNo..] (drop (startNo - 1) elections)]
