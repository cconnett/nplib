module Hash where

import Data.HashTable
import Data.Int
    
class Show a => Hash a where
    hash :: a -> Int32
    hash = hashString . show

instance Hash Int where
    hash = hashInt
instance Hash String where
    hash = hashString
