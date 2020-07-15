{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}

module Clash.GHC.PartialEval.Char where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Prim
import GHC.Types hiding (Type)

import Clash.Core.Evaluator.Models
import Clash.Core.Literal
import Clash.Core.Term

import Clash.GHC.PartialEval.Internal

charPrims :: HashMap Text PrimImpl
charPrims = HashMap.fromList
  [ ("GHC.Prim.gtChar#", charComparison gtChar#)
  , ("GHC.Prim.geChar#", charComparison geChar#)
  , ("GHC.Prim.eqChar#", charComparison eqChar#)
  , ("GHC.Prim.neChar#", charComparison neChar#)
  , ("GHC.Prim.ltChar#", charComparison ltChar#)
  , ("GHC.Prim.leChar#", charComparison leChar#)
  , ("GHC.Prim.ord#", primOrd)
  , ("GHC.Types.C#", primC)
  ]

primOrd :: PrimImpl
primOrd = liftUnary $ \x ->
  let !(C# a) = x in I# (ord# a)

primC :: PrimImpl
primC =
  liftBox $ \env dc x ->
    let !(C# _) = x in VData dc [Left $ Literal (CharLiteral x)] env

charComparison :: (Char# -> Char# -> Int#) -> PrimImpl
charComparison op =
  liftBinary $ \x y ->
    let !(C# a) = x
        !(C# b) = y
     in I# (a `op` b)

