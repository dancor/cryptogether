{-# LANGUAGE TemplateHaskell #-}

module Index where

import Control.Parallel.Strategies
import Data.DeriveTH
import Data.Serialize
import Data.Word
import qualified Data.Map as M

data Index = Index {
  indexVersion :: Word64,
  fileData :: M.Map FilePath [Word64]
  }

$(derive makeSerialize ''Index)
$(derive makeNFData ''Index)
