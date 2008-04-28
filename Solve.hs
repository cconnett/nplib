{-# OPTIONS -fglasgow-exts #-}

module Main
    where

import Manipulation
import ILPSAT
import SatSolvers
--import GLPKSolver
import System
import System.IO
import Voting
import Elections
import Debug.Trace
import Data.List
import Maybe
import Control.Monad
import Test.QuickCheck
import Solvers

satSolver = RSat

main = do
  args <- getArgs
  hSetBuffering stdin LineBuffering
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
                                "sat" -> possibleWinnersBySolver satSolver (read (args !! 1)) (head elections)
                                "hyb" -> hybridSolver (head elections)
                                          (possibleWinnersByBruteForce (read (args !! 1)))
                                          (possibleWinnersBySolver satSolver (read (args !! 1)) (head elections))
                                _     -> error "Supported methods are \nbf\nf2w\nsat\nhyb"
       sequence $
          [do let (theMinimumManipulatorsLower, theMinimumManipulatorsUpper) =
                      minimumManipulators winnerCalculator election
              putStrLn $ (show electionNo) ++ " lower: " ++ (show theMinimumManipulatorsLower)
              putStrLn $ (show electionNo) ++ " upper: " ++ (show theMinimumManipulatorsUpper)
              hFlush stdout
           | (electionNo, election) <- zip [startNo..] (drop (startNo - 1) elections)]
