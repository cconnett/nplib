import BruteForceSolver
import Elections
import Embeddings
import Manipulation
import ReductionComponents
import Reductions
import SatSolvers
import Utilities
import Voting hiding (beats)

import Control.Arrow
import Control.Monad
import Control.Monad.Writer
import Data.Bits
import Data.List
import Data.Maybe
import Data.Ord
import Data.Ratio
import Debug.Trace
import System.Exit
import Test.QuickCheck
import Text.Printf
import Text.Regex.Posix
import qualified Data.Map as M
import qualified Data.Set as S

flop (a,b) = (b,a)

mode = RSat

prop_doubleNegation prop = prop == (neg $ neg $ prop)
