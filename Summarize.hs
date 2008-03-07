import Elections
import System
import Voting
import Data.Maybe
import Data.List

main = do
  args <- getArgs
  if length args /= 1
     then error "Summarize electionsFile"
     else do
       let electionsFilename = (args !! 0) :: String
       electionsData <- readFile electionsFilename
       let elections = (read $ electionsData) :: [[Vote Int]]
           candidates = extractCandidates (head elections)
       mapM (\candidate -> putStrLn $ show $ scoringProtocolScore bordaS candidates (head elections) (Candidate candidate)) [1..length candidates]
       putStr $ unlines $ map ((unwords.(map (show.fromCandidate))).fromVote) (head elections)

scoringProtocolScore s candidates votes candidate = (candidate, score candidate)
    where score candidate = sum $ map (scoreList!!) $ mapMaybe (\vote -> (candidate `elemIndex` (fromVote vote))) votes
          scoreList = s $ fromIntegral $ length candidates

pluralityS :: Int -> [Int]
pluralityS = (\n -> 1:[0,0..])
bordaS = (\n -> [n-1,n-2..])
