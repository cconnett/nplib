module GLPKSolver where

import ILPSAT
import VarMapping
import Solvers
    
import Text.Regex.Posix
import Data.Maybe
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad
import System.IO
import System.Directory
import System.Process
import Foreign (unsafePerformIO)

data GLPK = GLPK
            
instance Solver GLPK where
    solveA s = glpsolA

-- Conversion of Problem instances to GNU MathProg (ILP)
toMathProg :: forall a. (Ord a) => [Constraint a] -> (M.Map (Proposition a) Int, String)
toMathProg lp = (varMapF, unlines $ concat $ map (\f -> f lp) $
                           [varLine1, objectiveLine, ineqLines varMapF, formulaLines varMapF, varLine2 varMapF, endLine])
    where varMapF :: M.Map (Proposition a) Int
          varMapF = M.fromAscList $ zip (S.toList $ foldr S.union S.empty $ map varSet lp) [0..]
varLine1 lp =
    ["set VARS;",
     "var thevar{i in VARS} binary;"]
varLine2 varMapF lp =
    ["data;",
     "set VARS := " ++ unwords (map show [0..numVars-1]) ++ ";"]
    where numVars = M.size varMapF
objectiveLine _ = ["maximize z: 0;"]
ineqLines varMapF lp = ["s.t. ineq" ++ show n ++ ":" ++ (concat $ intersperse " + " [show coeff ++ " * thevar[" ++ show (varMapF M.! (normalizeProposition var)) ++ "]"
                                                                                        | (coeff, var) <- lhs])
                       ++ " + 0 <= " ++ show rhs ++ ";"
                           | (n, (lhs, rhs)) <- zip [1..] $ map fromInequality $ filter isInequality lp]
formulaLines varMapF lp = ["s.t. formula" ++ show n ++ ":" ++ (concat $ intersperse " + " ["("++(if isNeg proposition then "-" else "") ++
                                                                                   "thevar[" ++ show (varMapF M.! (normalizeProposition proposition)) ++ "])"
                                                                                       | proposition <- fromClause clause])
                          ++ " >= " ++ show (1 - (length $ filter isNeg (fromClause clause))) ++ ";"
                              | (n, clause) <- zip [1..] $ filter (not.null.fromClause) $ fromFormula $ conjoin $ filter isFormula lp]
endLine _ = ["end;"]


{-# NOINLINE glpsolA #-}
glpsolA :: (Ord a) => Problem a -> (Bool, [Proposition a])
glpsolA problem = unsafePerformIO $ do
  (modname, modHandle) <- openTempFile "/tmp/" "glpk.mod"
  (solname, solHandle) <- openTempFile "/tmp/" "glpk.sol"
  hClose solHandle
  let (varMap, model) = toMathProg (detrivialize problem)
  hPutStr modHandle model
  hClose modHandle
  (inp, result, err, glpsolProcess) <-
      runInteractiveProcess "/usr/bin/glpsol"
                                ["--nopresol",
                                 "--memlim", "1024", -- 1 gigabyte
                                 "-m", modname, "-o", solname]
                                Nothing Nothing
  hClose inp
  hClose err
  readResult <- hGetContents result
  putStr (readResult `seq` "")
  --hClose result
  getProcessExitCode glpsolProcess
  --putStr $! readResult
  --removeFile tmpname
  glpsolParse problem varMap readResult (readFile solname)
  
glpsolParse :: (Ord a) => Problem a -> M.Map (Proposition a) Int -> String -> IO String -> IO (Bool, [Proposition a])
glpsolParse problem varMapF result ioSolution
    | solved = do solution <- ioSolution
                  return (True, catMaybes $ map ((liftM (varMapR M.!)).readMatch.(=~ "thevar\\[([0-9]+)\\].*?\\* *?1"))
                                  (lines solution))
    | trivial = return (True, [])
    | otherwise = return (False, [])
    where solved = result =~ "INTEGER OPTIMAL SOLUTION FOUND"
          trivial = result =~ "Problem has no columns" && (all (\(lhs, rhs) -> rhs >= 0) $ map fromInequality $ filter isInequality problem)
          varMapR = M.fromList $ map (\(a,b)->(b,a)) $
                    M.toList $ varMapF
          readMatch :: (String,String,String,[String]) -> Maybe Int
          readMatch (_, _, _, []) = Nothing
          readMatch (_, _, _, [thevar]) = Just (read thevar)
