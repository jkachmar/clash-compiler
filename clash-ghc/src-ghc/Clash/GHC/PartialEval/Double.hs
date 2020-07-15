{-# LANGUAGE CPP #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE UnboxedTuples #-}

module Clash.GHC.PartialEval.Double
  ( doublePrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Int
import GHC.Prim
import GHC.Types hiding (Type)

import Clash.Core.Evaluator.Models
import Clash.Core.Literal
import Clash.Core.Term

import Clash.GHC.PartialEval.Internal

doublePrims :: HashMap Text PrimImpl
doublePrims = HashMap.fromList
  [ ("GHC.Prim.>##", doubleComparison (>##))
  , ("GHC.Prim.>=##", doubleComparison (>=##))
  , ("GHC.Prim.==##", doubleComparison (==##))
  , ("GHC.Prim./=##", doubleComparison (/=##))
  , ("GHC.Prim.<##", doubleComparison (<##))
  , ("GHC.Prim.<=##", doubleComparison (<=##))
  , ("GHC.Prim.+##", liftBinary# (+##))
  , ("GHC.Prim.-##", liftBinary# (-##))
  , ("GHC.Prim.*##", liftBinary# (*##))
  , ("GHC.Prim./##", liftBinary# (/##))
  , ("GHC.Prim.negateDouble#", liftUnary# negateDouble#)
  , ("GHC.Prim.fabsDouble#", liftUnary# fabsDouble#)
  , ("GHC.Prim.double2Int#", primDouble2Int)
  , ("GHC.Prim.double2Float#", primDouble2Float)
  , ("GHC.Prim.expDouble#", liftUnary# expDouble#)
#if MIN_VERSION_ghc(8,10,0)
  , ("GHC.Prim.expm1Double#", liftUnary# expm1Double#)
#endif
  , ("GHC.Prim.logDouble#", liftUnary# logDouble#)
#if MIN_VERSION_ghc(8,10,0)
  , ("GHC.Prim.log1pDouble#", liftUnary# log1pDouble#)
#endif
  , ("GHC.Prim.sqrtDouble#", liftUnary# sqrtDouble#)
  , ("GHC.Prim.sinDouble#", liftUnary# sinDouble#)
  , ("GHC.Prim.cosDouble#", liftUnary# cosDouble#)
  , ("GHC.Prim.tanDouble#", liftUnary# tanDouble#)
  , ("GHC.Prim.asinDouble#", liftUnary# asinDouble#)
  , ("GHC.Prim.acosDouble#", liftUnary# acosDouble#)
  , ("GHC.Prim.atanDouble#", liftUnary# atanDouble#)
  , ("GHC.Prim.sinhDouble#", liftUnary# sinhDouble#)
  , ("GHC.Prim.coshDouble#", liftUnary# coshDouble#)
  , ("GHC.Prim.tanhDouble#", liftUnary# tanhDouble#)

#if MIN_VERSION_ghc(8,7,0)
  , ("GHC.Prim.asinhDouble#", liftUnary# asinhDouble#)
  , ("GHC.Prim.acoshDouble#", liftUnary# acoshDouble#)
  , ("GHC.Prim.atanhDouble#", liftUnary# atanhDouble#)
#endif

#if MIN_VERSION_base(4,12,0)
  , ("GHC.Float.$w$casinh", primAsinhSpecialized)
#endif

  , ("GHC.Prim.**##", liftBinary# (**##))
  , ("GHC.Prim.decodeDouble_2Int#", primDecodeDouble2Int)
  , ("GHC.Prim.decodeDouble_Int64#", primDecodeDoubleInt64)
  , ("GHC.Types.D#", primD)
  ]

primDouble2Int :: PrimImpl
primDouble2Int =
  liftUnary $ \x ->
    let !(D# a) = x in I# (double2Int# a)

primDouble2Float :: PrimImpl
primDouble2Float =
  liftUnary $ \x ->
    let !(D# a) = x in F# (double2Float# a)

#if MIN_VERSION_base(4,12,0)
primAsinhSpecialized :: PrimImpl
primAsinhSpecialized =
  liftUnary# $ \x ->
    let !(D# a) = asinh (D# x) in a
#endif

primDecodeDouble2Int :: PrimImpl
primDecodeDouble2Int =
  liftUnary $ \x ->
    let !(D# a) = x
        !(# b, c, d, e #) = decodeDouble_2Int# a
     in (I# b, W# c, W# d, I# e)

primDecodeDoubleInt64 :: PrimImpl
primDecodeDoubleInt64 =
  liftUnary $ \x ->
    let !(D# a) = x
        !(# b, c #) = decodeDouble_Int64# a
     in (I64# b, I# c)

primD :: PrimImpl
primD =
  liftBox $ \env dc x ->
    let !(D# _) = x
     in VData dc [Left $ Literal (DoubleLiteral (toRational x))] env

liftUnary# :: (Double# -> Double#) -> PrimImpl
liftUnary# op =
  liftUnary $ \x ->
    let !(D# a) = x in D# (op a)

liftBinary# :: (Double# -> Double# -> Double#) -> PrimImpl
liftBinary# op =
  liftBinary $ \x y ->
    let !(D# a) = x
        !(D# b) = y
     in D# (a `op` b)

doubleComparison :: (Double# -> Double# -> Int#) -> PrimImpl
doubleComparison op =
  liftBinary $ \x y ->
    let !(D# a) = x
        !(D# b) = y
     in I# (a `op` b)

