{-# OPTIONS -fglasgow-exts #-}

-- The primary convenience type for non-deterministic programming
-- provided by nplib is a representation of a non-deterministic
-- integer.  A non-deterministic integer is represented in a sat
-- formula by a list of variables in a formula.  Each variable
-- represents one bit of the integer.  When the formula is solved by a
-- sat solver and the variables assigned truth values, the truth
-- values of each variable determine the value of the
-- non-deterministic integer.  For example, if an integer has the list
-- of variables [1,2,3,4,5,6,7,8], and the satisfying assignment
-- generated by the sat solver assigns them the truth values [False,
-- False, True, True, False, True, True, True] respectively (leftmost
-- variables are most significant), then the integer can be
-- interpreted to have value 00110111 in base 2, and the value 55 in
-- base 10.
--
-- Currently there is no explicit differentiation between signed and
-- unsigned numbers.  Reductions constructed by this library
-- performing arithmetic on non-deterministic integers will respect
-- using two's complement representation for negative values.  That
-- is, if known negative values are represented in two's complement,
-- the assignments to the unknowns will be correct if interpreted as
-- two's complement.

module NInteger where

import NProgram
import SAT
import Control.Monad.State
import Control.Arrow
import Data.Bits
import Data.Word

import Utilities

newtype NInt = NInt [Var]
newtype NUInt = NUInt [Var]

newtype NBool = NBool [Var]
false = NBool [falseVar]
true = NBool [trueVar]

instance NVar NInt where
    toVars (NInt vars) = vars
    fromVars = NInt
instance Interpret NInt Int where
    interpret v = fromIntegral . asSignedInteger
               
instance NVar NUInt where
    toVars (NUInt vars) = vars
    fromVars = NUInt
instance Interpret NUInt Int where
    interpret v = fromIntegral . asUnsignedInteger
    
instance NVar NBool where
    toVars (NBool vars) = vars
    fromVars = NBool
instance Interpret NBool Bool where
    interpret v = asBool


class NVar k => NIntegral k where
    new :: Int -> State NProgram k
    new width = do
      newVars <- takeSatVars width
      return $ fromVars newVars

    fromInteger :: Integer -> State NProgram k
    fromInteger i = do
      it <- new 16
      let varStatuses = map (first (testBit i)) $ zip [width it - 1, width it - 2 .. 0] (toVars it)
      forM_ varStatuses $ \(isSet, var) ->
          assert $ (if isSet then makeTrue else makeFalse) var
      return it

    width :: k -> Int
    width = length . toVars

    extendTo :: Int -> k -> k
    extendTo bits k =
        let vars = toVars k in
        fromVars $ replicate (bits - length vars) (head vars) ++ vars
    
instance NIntegral NInt
instance NIntegral NUInt
instance NIntegral NBool

trueIndices bools = map fst $ filter snd $ zip [0..] (reverse bools)

asBool = or

asUnsignedInteger :: [Bool] -> Integer
asUnsignedInteger bools = foldl (.|.) 0 (map bit $ trueIndices bools)

asSignedInteger :: [Bool] -> Integer
asSignedInteger bools =
    let signBit = head (myTrace (concatMap (\b -> if b then "1" else "0") bools) bools)
        magnitude = asUnsignedInteger (tail bools)
    in
      if not signBit then
          magnitude else
          complement magnitude + 1

extendToCommonWidth a b c =
    let commonWidth = maximum $ map width $ [a,b,c]
    in
      (extendTo commonWidth a,
       extendTo commonWidth b,
       extendTo commonWidth c)

-- only works on same width integrals
equal :: NIntegral k => k -> k -> Stateful Formula
equal a b = (liftM conjoin) $
            forM (zip (toVars a) (toVars b)) (return . uncurry makeEquivalent)

add :: NIntegral k => k -> k -> k -> Stateful Formula
add c a b = do
  let (a', b', c') = extendToCommonWidth a b c
  let theWidth = width a' -- == width b' == width c'
  let numCarryBits = theWidth - 1
  carryBits <- takeSatVars numCarryBits
  let aBit k = Merely $ (toVars a') !! (theWidth - k - 1)
  let bBit k = Merely $ (toVars b') !! (theWidth - k - 1)
  let cBit k = Merely $ (toVars c') !! (theWidth - k - 1)
  let carryBit k = Merely $ carryBits !! (numCarryBits - k)
  let set0thResult = Formula $ map Clause $
       [[      cBit 0,       aBit 0, neg $ bBit 0],
        [      cBit 0, neg $ aBit 0,       bBit 0],
        [neg $ cBit 0, neg $ aBit 0, neg $ bBit 0],
        [neg $ cBit 0,       aBit 0,       bBit 0]]
  let set1stCarry = Formula $ map Clause $
       [[      carryBit 1, neg $ aBit 0, neg $ bBit 0],
        [neg $ carryBit 1,       aBit 0              ],
        [neg $ carryBit 1,                     bBit 0]]
  let setKthResult k = Formula $ map Clause $
       [[      cBit k, neg $ aBit k,       bBit k,       carryBit k],
        [      cBit k, neg $ aBit k, neg $ bBit k, neg $ carryBit k],
        [      cBit k,       aBit k, neg $ bBit k,       carryBit k],
        [      cBit k,       aBit k,       bBit k, neg $ carryBit k],
        [neg $ cBit k,       aBit k,       bBit k,       carryBit k],
        [neg $ cBit k,       aBit k, neg $ bBit k, neg $ carryBit k],
        [neg $ cBit k, neg $ aBit k, neg $ bBit k,       carryBit k],
        [neg $ cBit k, neg $ aBit k,       bBit k, neg $ carryBit k]]
  let setKthCarry k = Formula $ map Clause $
       [[      carryBit k, neg $ aBit (k-1), neg $ bBit (k-1)                      ],
        [      carryBit k, neg $ aBit (k-1),                   neg $ carryBit (k-1)],
        [      carryBit k,                   neg $ bBit (k-1), neg $ carryBit (k-1)],
        [neg $ carryBit k,       aBit (k-1),       bBit (k-1)                      ],
        [neg $ carryBit k,       aBit (k-1),                         carryBit (k-1)],
        [neg $ carryBit k,                         bBit (k-1),       carryBit (k-1)]]
  return $ conjoin $
             [set0thResult, set1stCarry,
              conjoin $ map setKthResult [1 .. theWidth - 1],
              conjoin $ map setKthCarry [2 .. theWidth - 1]]

-- c == a - b <=> a == b + c
sub c a b = add a b c

-- Arithmetic shift left and right
x `shl` i = fromVars . (++ replicate i falseVar) . toVars
x `shr` i = fromVars . reverse . drop i . reverse . toVars