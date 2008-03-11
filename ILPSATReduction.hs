module ILPSATReduction where

import ILPSAT
--import Embeddings

import Data.Bits
import Data.List
import qualified Data.HashTable as HT

import Debug.Trace
import Utilities
    
-- Conversion from ILP to SAT, ala Warners, Joost, "A Linear-Time
-- Transformation of Linear Inequalities into Conjunctive Normal
-- Form."  The resulting Constraint is a Formula.
toSAT :: Show a => Problem a -> Problem a
toSAT p = concatMap convert (zip [0..] p)
    where convert (i, Formula formula) = [Formula formula]
          convert (i, TopFormula formula) = [TopFormula formula]
          convert (i, Inequality inequality) = trans i (Inequality inequality)

-- Conversion from SAT to ILP.  SAT is a special case of ILP, so the
-- reduction is straightforward.
toILP :: Problem a -> [Constraint a]
toILP p =
    -- split problem into inequalities and one big cnf formula
    let (priorInequalities, priorFormulas) = partition isInequality p
        rawFormula = concat $ map (\(Formula formula) -> formula) priorFormulas
    in
      priorInequalities ++ map clauseToInequality rawFormula

-- When converting SAT into ILP
clauseToInequality :: Clause a -> Constraint a
clauseToInequality clause = Inequality $
    -- negative literals with coeff -1 each
    ([(-1, normalizeProposition proposition) | proposition <- fromClause clause, isPos proposition] ++ 
     -- positive literals with coeff 1 each
     [( 1, normalizeProposition proposition) | proposition <- fromClause clause, isNeg proposition], 
     -- b
     -1 + (length $ filter isNeg (fromClause clause)))

-- Warners' [War98] primary function --- converts an ILP inequality to a SAT formula
trans :: Show a => Int -> Constraint a -> Problem a
trans ineqNumber it@(Inequality (coeffsAndProps, b)) =
    --trace ("transing " ++ show it ++ " yields") $
    --traceIt $
            [pushTL $
             transLHS ineqNumber nonTrivialSummands,
             transRHS ineqNumber nonTrivialProps newB (sum $ map abs coeffs)
            ]
    where newB = b - (sum $ filter (<0) $ coeffs)
          -- To account for negative coefficients, increase b by their
          -- absolute sum.  Trans-ing functions will emit (neg
          -- variable) instead of variable when they detect the
          -- negative coefficient.
          nonTrivialSummands = filter ((/=0) . fst) coeffsAndProps
          coeffs = map fst coeffsAndProps
          nonTrivialProps = map snd nonTrivialSummands

transLHS :: Show a => Int -> [(Int, Proposition a)] -> Constraint a
transLHS ineqNumber [] = Formula []
transLHS ineqNumber summands = transLHS' ineqNumber aMax summands
    where aMax = maximum $ map (abs . fst) summands

transLHS' ineqNumber aMax [] = undefined
transLHS' ineqNumber aMax [(ai, var)] = tMul ineqNumber aMax ai var
transLHS' ineqNumber aMax summands = conjoin [transLHS' ineqNumber aMax bottom,
                                              transLHS' ineqNumber aMax top,
                                              tAdd ineqNumber aMax (map snd bottom) (map snd top)]
    where bottom = take half summands
          top = drop half summands
          half = ceiling $ (fromIntegral $ length summands) / 2

transRHS :: (Show a) => Int -> [Proposition a] -> Int -> Int -> Constraint a
transRHS ineqNumber varSet b coeffMagnitude =
    --trace (show coeffMagnitude) $
    case b of
      b | b < 0 -> 
          -- unsatisfiable RHS: produce a trivially unsatisfiable Formula
          Formula [Clause [Auxiliary (-1) "X" (-1) varSet], Clause [neg $ Auxiliary (-1) "X" (-1) varSet]]
      b | b > coeffMagnitude ->
          -- RHS is bigger than the LHS could ever be: trivially satisifiable
          Formula []
      otherwise ->
          Formula $ map Clause [[neg $ Auxiliary ineqNumber "p" k varSet] ++
                                [neg $ Auxiliary ineqNumber "p" j varSet | j <- all, testBit b j, j > k]
                                | k <- all, not (testBit b k)]
    where --all = [0..m (max b coeffMagnitude) - 1]
          all = [0..m coeffMagnitude - 1]

m 0 = 0
m i = (1+) . floor . (logBase 2) . fromIntegral $ i

tAdd :: (Show a) => Int -> Int -> [Proposition a] -> [Proposition a] -> Constraint a
tAdd ineqNumber aMax v w | length v < length w = tAdd ineqNumber aMax w v
tAdd ineqNumber aMax v w =
    --trace ("mu " ++ show mu ++ " " ++ show mv ++ " " ++ show mw) $
    conjoin $ [extendW, f11, f12, conjoin $ map f13 [1..mu - 2], conjoin $ map f14 [1..mu - 2],
               if mu == mv {-No extra carried bit-} then f13 (mu-1) else f8]
        where u = v ++ w
              mu = m (aMax * length u)
              mv = m (aMax * length v)
              mw = m (aMax * length w)
              --t2 = if ineqNumber == 1002001000 then trace else (flip const)
              extendW = Formula [{-t2 (show i ++ " " ++ show w) $ -} Clause [neg $ pTerm i w] | i <- [mw..mv-1]]
              f11 = Formula $ map Clause $
                    [[      pTerm 0 u,       pTerm 0 v, neg $ pTerm 0 w],
                     [      pTerm 0 u, neg $ pTerm 0 v,       pTerm 0 w],
                     [neg $ pTerm 0 u, neg $ pTerm 0 v, neg $ pTerm 0 w],
                     [neg $ pTerm 0 u,       pTerm 0 v,       pTerm 0 w]]
              f12 = Formula $ map Clause $
                    [[      cTerm 1 u, neg $ pTerm 0 v, neg $ pTerm 0 w],
                     [neg $ cTerm 1 u,       pTerm 0 v                 ],
                     [neg $ cTerm 1 u,                        pTerm 0 w]]
              f13 k = Formula $ map Clause $
                      [[      pTerm k u, neg $ pTerm k v,       pTerm k w,       cTerm k u],
                       [      pTerm k u, neg $ pTerm k v, neg $ pTerm k w, neg $ cTerm k u],
                       [      pTerm k u,       pTerm k v, neg $ pTerm k w,       cTerm k u],
                       [      pTerm k u,       pTerm k v,       pTerm k w, neg $ cTerm k u],
                       [neg $ pTerm k u,       pTerm k v,       pTerm k w,       cTerm k u],
                       [neg $ pTerm k u,       pTerm k v, neg $ pTerm k w, neg $ cTerm k u],
                       [neg $ pTerm k u, neg $ pTerm k v, neg $ pTerm k w,       cTerm k u],
                       [neg $ pTerm k u, neg $ pTerm k v,       pTerm k w, neg $ cTerm k u]]
              f14 k = Formula $ map Clause $
                      [[      cTerm (k+1) u, neg $ pTerm k v, neg $ pTerm k w                 ],
                       [      cTerm (k+1) u, neg $ pTerm k v,                  neg $ cTerm k u],
                       [      cTerm (k+1) u,                  neg $ pTerm k w, neg $ cTerm k u],
                       [neg $ cTerm (k+1) u,       pTerm k v,       pTerm k w                 ],
                       [neg $ cTerm (k+1) u,       pTerm k v,                        cTerm k u],
                       [neg $ cTerm (k+1) u,                        pTerm k w,       cTerm k u]]
              f8 = Formula $ map Clause $
                   [[      pTerm (mu-1) u, neg $ cTerm (mu-1) u],
                    [neg $ pTerm (mu-1) u,       cTerm (mu-1) u]]

              pTerm k varSet = Auxiliary ineqNumber "p" k varSet
              cTerm k varSet = Auxiliary ineqNumber "c" k varSet

tMul :: forall a. Int -> Int -> Int -> Proposition a -> Constraint a
tMul ineqNumber aMax ai prop =
    conjoin $ [(if testBit (abs ai) k then clausesTrue else clausesFalse) k prop
              | k <- [0..m aMax - 1]]
        where clausesTrue k prop = Formula [Clause [neg $ pTerm k [prop], propInverter $     prop],
                                            Clause [      pTerm k [prop], propInverter $ neg prop]]
              clausesFalse k prop = Formula [Clause [neg $ pTerm k [prop]]]
              propInverter :: Proposition a -> Proposition a
              propInverter = if ai < 0 then neg else id
              pTerm k propSet = Auxiliary ineqNumber "p" k propSet
              cTerm k propSet = Auxiliary ineqNumber "c" k propSet
