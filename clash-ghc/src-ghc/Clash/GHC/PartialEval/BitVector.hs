{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.BitVector
  ( bitVectorPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)

import Clash.Sized.Internal.BitVector

import Clash.GHC.PartialEval.Internal

bitVectorPrims :: HashMap Text PrimImpl
bitVectorPrims = HashMap.fromList
  [ ("Clash.Sized.Internal.BitVector.fromInteger#", liftId)
  , ("Clash.Sized.Internal.BitVector.+#", liftBinarySized (const id) _)
  ]

