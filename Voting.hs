{-# OPTIONS -fno-monomorphism-restriction -fglasgow-exts #-}

module Voting
    where

import Data.List
import Data.Maybe
import Data.Ord
import Data.Ratio
import Debug.Trace

--Basic defitions

data Candidate a = Candidate !a
    deriving (Show, Eq, Ord, Read)

data Vote a = Vote ![Candidate a]
    deriving (Show, Eq, Ord, Read)

-- Uniform type for voting rules: take a list of candidates, a list of
-- votes, and selects a candidate from the list of candidates as the
-- winner.
type Rule a = [Candidate a] -> [Vote a] -> [Candidate a]

instance (Eq a) => Read (Rule a) where
    readsPrec _ "irv" = [(irv, "")]
    readsPrec _ "coombs" = [(coombs, "")]
    readsPrec _ "plurality" = [(plurality, "")]
    readsPrec _ "pluralityWithRunoff" = [(pluralityWithRunoff, "")]
    readsPrec _ "borda" = [(borda, "")]
    readsPrec _ "veto" = [(veto, "")]
    --readsPrec _ "bucklin" = [(bucklin, "")]
    readsPrec _ "copeland" = [(copeland (1%2), "")]
    readsPrec _ "maximin" = [(maximin, "")]
    readsPrec _ _ = error $ "Supported rules are\n" ++
                    (unlines rules)

rules :: [String]
rules = ["irv", "coombs", "plurality", "pluralityWithRunoff", "borda", "veto",
         --"bucklin",
         "copeland", "maximin"]

-- True iff candidate a is strictly before candidate b in the given vote
beats :: (Eq a) => Vote a -> Candidate a -> Candidate a -> Bool
beats (Vote (c:rest)) a b
    | a == b = False
    | c == a = True
    | c == b = False
    | otherwise = beats (Vote rest) a b

marginOfVictory :: (Eq a) => [Vote a] -> Candidate a -> Candidate a -> Int
marginOfVictory votes a b = (length $ filter (==True) results) -
                       (length $ filter (==False) results)
    where results = map (\vote -> beats vote a b) votes

defeats, ties :: (Eq a) => [Vote a] -> Candidate a -> Candidate a -> Bool
defeats votes a b = marginOfVictory votes a b > 0
ties votes a b = marginOfVictory votes a b == 0

firstPlaceVotes :: (Eq a) => [Vote a] -> Candidate a -> Int
firstPlaceVotes votes candidate = length $ filter (==candidate) $ map (head.fromVote) votes

lastPlaceVotes :: (Eq a) => [Vote a] -> Candidate a -> Int
lastPlaceVotes votes candidate = length $ filter (==candidate) $ map (last.fromVote) votes
                                  
-- wrt removes from a vote v candidates not in s
wrt :: (Eq a) => Vote a -> [Candidate a] -> Vote a
wrt (Vote v) s = Vote $ filter (`elem` s) v

extractCandidates votes = nub $ concatMap fromVote votes
fromVote (Vote v) = v
fromCandidate (Candidate c) = c

equating f a b = f a == f b
topGroupBy scoreFunction =
    head . (groupBy (equating scoreFunction)) .
            (sortBy (comparing ((0-).scoreFunction)))
                 
-- Voting methods
scoringProtocol :: (Eq a, Integral k, Real g) => (k -> [g]) -> Rule a
scoringProtocol s candidates votes = topGroupBy score candidates
    where score candidate = sum $ map (scoreList!!) $ mapMaybe (\vote -> (candidate `elemIndex` (fromVote vote))) votes
          scoreList = s $ fromIntegral $ length candidates

plurality = scoringProtocol (\n -> 1:[0,0..])
borda = scoringProtocol (\n -> [n-1, n-2 .. 0])
veto = scoringProtocol (\n -> (replicate (n-1) 1) ++ [0])
amazonUnspun = scoringProtocol (\n -> map (1000/) [1..])
scaleFree = scoringProtocol (\n -> map (\i -> exp (-i)) [1..])

pluralityWithRunoff :: (Eq a) => Rule a
pluralityWithRunoff candidates votes =
    topGroupBy (firstPlaceVotes (map (`wrt`runoffCandidates) votes)) runoffCandidates
    where runoffCandidates = let groupA : ~(groupB:rest) =
                                     groupBy (equating (firstPlaceVotes votes)) $
                                     reverse $
                                     sortBy (comparing (firstPlaceVotes votes)) candidates
                             in if length groupA >= 2 then groupA else groupA++groupB
          --candidates = extractCandidates votes

irv :: (Eq a) => Rule a
irv candidates votes
    | length remainingCandidates == 0 = candidates
    | otherwise = irv remainingCandidates $ map (`wrt`remainingCandidates) votes
    where remainingCandidates = candidates \\ losers
          losers = topGroupBy ((0-).(firstPlaceVotes votes)) candidates

coombs :: (Eq a) => Rule a
coombs candidates votes
    | length remainingCandidates == 0 = candidates
    | otherwise = coombs remainingCandidates $ map (`wrt`remainingCandidates) votes
    where remainingCandidates = candidates \\ losers
          losers = topGroupBy (lastPlaceVotes votes) candidates

-- Condorcet pairwise table: list of votes to ... something ...

--pwt :: (Eq a) => [Vote a] -> [((Candidate a, Candidate a), Int)]
--pwt candidates votes = [((x, y), marginOfVictory x y) | x <- candidates, y <- candidates, x /= y]

maximin :: (Eq a) => Rule a
maximin candidates votes = topGroupBy worstLoss candidates
    where worstLoss c = minimum (map (marginOfVictory votes c) (delete c candidates))

copeland :: (Eq a) => Ratio Int -> Rule a
copeland tieValue candidates votes = topGroupBy (copelandScore tieValue) candidates
    where copelandScore tieValue c =
              ((length $ filter (c `defeatsV`) otherCandidates) % 1) +
              tieValue * ((length $ filter (c `tiesV`) otherCandidates) % 1)
              where otherCandidates = delete c candidates
          defeatsV = defeats votes
          tiesV = ties votes

{-
bucklin :: (Eq a) => Rule a
bucklin candidates votes = head $ catMaybes $ map (bucklinStep candidates votes) [1..length candidates]

bucklinStep :: (Eq a) => [Candidate a] -> [Vote a] -> Int -> Maybe (Candidate a)
bucklinStep candidates votes k = if null winners then Nothing else Just $ snd $ head winners
    where tiesEliminatedWinners = if length winners > 1 && fst (winners !! 0) == fst (winners !! 1)
                                  then [] else winners
          winners = takeWhile (\(score,cand) -> score > (ceiling $ (fromIntegral $ length votes)/2)) $
                    map (\sublist -> (length sublist, head sublist)) $
                    reverse $
                    sortBy (comparing length) $
                    group $
                    sortBy (comparing (\(Candidate c) -> c)) $
                    concatMap ((take k).fromVote) votes
-}
approval :: (Eq a, Ord a, Show a) => Int -> Rule a
approval k = scoringProtocol (\n -> replicate k 1 ++ repeat 0)
