{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Natural
  ( naturalPrims
  ) where

import Control.Monad.Trans.Class
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Natural
import GHC.Types

import Clash.Core.Evaluator.Models
import Clash.Core.Literal
import Clash.Core.Term

import Clash.GHC.PartialEval.Internal

naturalPrims :: HashMap Text PrimImpl
naturalPrims = HashMap.fromList
  [ ("GHC.Natural.naturalToInteger", liftUnary naturalToInteger)
  , ("GHC.Natural.naturalFromInteger", liftUnary naturalFromInteger)
  , ("GHC.Natural.plusNatural", liftBinary plusNatural)
  , ("GHC.Natural.timesNatural", liftBinary timesNatural)
  , ("GHC.Natural.minusNatural", liftBinary minusNatural)
  , ("GHC.Natural.wordToNatural#", primWordToNatural)
  , ("GHC.Natural.gcdNatural", liftBinary gcdNatural)
--, ("GHC.Natural.$wshiftLNatural", _)
  , ("GHC.Natural.NatS#", primNatS)
  ]

primWordToNatural :: PrimImpl
primWordToNatural =
  liftUnary $ \x ->
    let !(W# a) = x in wordToNatural# a

primNatS :: PrimImpl
primNatS e p args = do
  env <- lift getLocalEnv
  [natS, _natJ] <- typeDcs (primType p)
  liftUnary (go env natS) e p args
 where
  go env dc x =
    let !(W# _) = x
     in VData dc [Left $ Literal (WordLiteral (toInteger x))] env

