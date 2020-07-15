{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnboxedTuples #-}

module Clash.GHC.PartialEval.Int
  ( intPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Prim
import GHC.Types hiding (Type)

import Clash.Core.Evaluator.Models
import Clash.Core.Literal
import Clash.Core.Term

import Clash.GHC.PartialEval.Internal

intPrims :: HashMap Text PrimImpl
intPrims = HashMap.fromList
  [ ("GHC.Prim.+#", liftBinary# (+#))
  , ("GHC.Prim.-#", liftBinary# (-#))
  , ("GHC.Prim.*#", liftBinary# (*#))
  , ("GHC.Prim.mulIntMayOflo#", liftBinary# mulIntMayOflo#)
  , ("GHC.Prim.quotInt#", liftBinary# quotInt#)
  , ("GHC.Prim.remInt#", liftBinary# remInt#)
  , ("GHC.Prim.quotRemInt#", liftI_I_II quotRemInt#)
  , ("GHC.Prim.andI#", liftBinary# andI#)
  , ("GHC.Prim.orI#", liftBinary# orI#)
  , ("GHC.Prim.xorI#", liftBinary# xorI#)
  , ("GHC.Prim.notI#", liftUnary# notI#)
  , ("GHC.Prim.negateInt#", liftUnary# negateInt#)
  , ("GHC.Prim.addIntC#", liftI_I_II addIntC#)
  , ("GHC.Prim.subIntC#", liftI_I_II subIntC#)
  , ("GHC.Prim.>#", liftBinary# (>#))
  , ("GHC.Prim.>=#", liftBinary# (>=#))
  , ("GHC.Prim.==#", liftBinary# (==#))
  , ("GHC.Prim./=#", liftBinary# (/=#))
  , ("GHC.Prim.<#", liftBinary# (<#))
  , ("GHC.Prim.<=#", liftBinary# (<=#))
  , ("GHC.Prim.chr#", primChr)
  , ("GHC.Prim.int2Word#", primInt2Word)
  , ("GHC.Prim.int2Float#", primInt2Float)
  , ("GHC.Prim.int2Double#", primInt2Double)
  , ("GHC.Prim.word2Float#", primWord2Float)
  , ("GHC.Prim.word2Double#", primWord2Double)
  , ("GHC.Prim.uncheckedIShiftL#", liftBinary# uncheckedIShiftL#)
  , ("GHC.Prim.uncheckedIShiftRA#", liftBinary# uncheckedIShiftRA#)
  , ("GHC.Prim.uncheckedIShiftRL#", liftBinary# uncheckedIShiftRL#)
  , ("GHC.Types.I#", primI)
  , ("GHC.Types.I8#", primI)
  , ("GHC.Types.I16#", primI)
  , ("GHC.Types.I32#", primI)
  , ("GHC.Types.I64#", primI)
  ]

primChr :: PrimImpl
primChr =
  liftUnary $ \i ->
    let !(I# a) = i in C# (chr# a)

primInt2Word :: PrimImpl
primInt2Word =
  liftUnary $ \i ->
    let !(I# a) = i in W# (int2Word# a)

primInt2Float :: PrimImpl
primInt2Float =
  liftUnary $ \i ->
    let !(I# a) = i in F# (int2Float# a)

primInt2Double :: PrimImpl
primInt2Double =
  liftUnary $ \i ->
    let !(I# a) = i in D# (int2Double# a)

primWord2Float :: PrimImpl
primWord2Float =
  liftUnary $ \i ->
    let !(W# a) = i in F# (word2Float# a)

primWord2Double :: PrimImpl
primWord2Double =
  liftUnary $ \i ->
    let !(W# a) = i in D# (word2Double# a)

primI :: PrimImpl
primI =
  liftBox $ \env dc x ->
    let !(I# _) = x
     in VData dc [Left $ Literal (IntLiteral (toInteger x))] env

liftUnary# :: (Int# -> Int#) -> PrimImpl
liftUnary# op =
  liftUnary $ \i ->
    let !(I# a) = i in I# (op a)

liftBinary# :: (Int# -> Int# -> Int#) -> PrimImpl
liftBinary# op =
  liftBinary $ \i j ->
    let !(I# a) = i
        !(I# b) = j
     in I# (a `op` b)

liftI_I_II :: (Int# -> Int# -> (# Int#, Int# #)) -> PrimImpl
liftI_I_II op =
  liftBinary $ \x y ->
    let !(I# a) = x
        !(I# b) = y
        !(# c, d #) = op a b
     in (I# c, I# d)

