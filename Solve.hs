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

satSolver = Minisat

pullElections electionsRaw electionsList =
    map (\i -> (i, electionsRaw!!(i-1))) electionsList

main = do
  args <- getArgs
  hSetBuffering stdout LineBuffering
  if length args < 3
     then error "Solve method rule electionsFile [electionsList]"
     else do
       let electionsFilename = (args !! 2) :: String
       electionsRaw <- readElections electionsFilename
       let elections = if length args >= 4 then
                           pullElections electionsRaw (map read $ drop 3 args) else
                           zip [1..] electionsRaw
       let method = args !! 0
           winnerCalculator = case method of
                                "bf"  -> possibleWinnersByBruteForce (read (args !! 1))
                                "f2w" -> findTwoWinners (read (args !! 1))
                                "sat" -> possibleWinnersBySolver satSolver (read (args !! 1)) (snd $ head elections)
                                "hyb" -> hybridSolver (snd $ head elections)
                                          (possibleWinnersByBruteForce (read (args !! 1)))
                                          (possibleWinnersBySolver satSolver (read (args !! 1)) (snd $ head elections))
                                _     -> error "Supported methods are \nbf\nf2w\nsat\nhyb"
       sequence $
          [do let (theMinimumManipulatorsLower, theMinimumManipulatorsUpper) =
                      minimumManipulators winnerCalculator election
              putStrLn $ (show electionNo) ++ " lower: " ++ (show theMinimumManipulatorsLower)
              putStrLn $ (show electionNo) ++ " upper: " ++ (show theMinimumManipulatorsUpper)
              hFlush stdout
           | (electionNo, election) <- elections]
