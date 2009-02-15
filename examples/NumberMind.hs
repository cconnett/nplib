module Main where

import NInteger
import Control.Monad.State
import SatSolvers
import NPLib
import Embeddings
import Tracing

numbermind info = do
  numbers :: [NInteger] <- replicateM 16 (newNInteger 5)
  mapM (`leq`(NInteger.fromInteger 9)) numbers >>= assertAll
  mapM ((NInteger.fromInteger 0)`leq`) numbers >>= assertAll
  mapM_ (\(guess, numCorrect) -> assertGuess numbers guess numCorrect) info
  return numbers
assertGuess :: [NInteger] -> Integer -> Integer -> NProgramComputation ()
assertGuess numbers guess numCorrect = do
  let guessDigits = map NInteger.fromInteger $
                    map read $ map (:[]) $ show guess
  digitGuessEqualities <- mapM (uncurry equal) $ zip numbers guessDigits
  digitGuessEqVars <- embedFormulas digitGuessEqualities
  --ntrace "digit guess equality" digitGuessEqVars (show :: [Bool]->String)
  actualNumCorrect <- nsum digitGuessEqVars
  --ntrace "actual num correct" actualNumCorrect (show::Integer->String)
  guess <- equal (NInteger.fromInteger numCorrect) actualNumCorrect
  return ()
  assert guess
main = print $
       concatMap show $ (snd $
       evalNProgram Minisat $
       numbermind
       [(5616185650518293, 2),
        (3847439647293047, 1),
        (5855462940810587, 3),
        (9742855507068353, 3),
        (4296849643607543, 3),
        (3174248439465858, 1),
        (4513559094146117, 2),
        (7890971548908067, 3),
        (8157356344118483, 1),
        (2615250744386899, 2),
        (8690095851526254, 3),
        (6375711915077050, 1),
        (6913859173121360, 1),
        (6442889055042768, 2),
        (2321386104303845, 0),
        (2326509471271448, 2),
        (5251583379644322, 2),
        (1748270476758276, 3),
        (4895722652190306, 1),
        (3041631117224635, 3),
        (1841236454324589, 3),
        (2659862637316867, 2)] :: [Integer])
