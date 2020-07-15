{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
--{-# LANGUAGE UnboxedTuples #-}

module Clash.GHC.PartialEval.Integer
  ( integerPrims
  ) where

import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap (fromList)
import Data.Text (Text)
import GHC.Integer.GMP.Internals
import GHC.Integer.Logarithms
import GHC.Prim
import GHC.Types

import Clash.GHC.PartialEval.Internal

integerPrims :: HashMap Text PrimImpl
integerPrims = HashMap.fromList
  [ ("GHC.Integer.Logarithms.integerLogBase#", primIntegerLogBase)

    -- Construct Integers
  , ("GHC.Integer.Type.smallInteger", primSmallInteger)
  , ("GHC.Integer.Type.wordToInteger", primWordToInteger)

    -- Conversion to other integral types
  , ("GHC.Integer.Type.integerToWord", primIntegerToWord)
  , ("GHC.Integer.Type.integerToInt", primIntegerToInt)

    -- Helpers for RealFloat type-class operations
  , ("GHC.Integer.Type.encodeFloatInteger", primEncodeFloatInteger)
  , ("GHC.Integer.Type.floatFromInteger", primFloatFromInteger)
  , ("GHC.Integer.Type.encodeDoubleInteger", primEncodeDoubleInteger)
--, ("GHC.Integer.Type.decodeDoubleInteger", primDecodeDoubleInteger)
  , ("GHC.Integer.Type.doubleFromInteger", primDoubleFromInteger)

    -- Arithmetic operations
  , ("GHC.Integer.Type.plusInteger", liftBinary plusInteger)
  , ("GHC.Integer.Type.minusInteger", liftBinary minusInteger)
  , ("GHC.Integer.Type.timesInteger", liftBinary timesInteger)
  , ("GHC.Integer.Type.negateInteger", liftUnary negateInteger)
  , ("GHC.Integer.Type.absInteger", liftUnary absInteger)
  , ("GHC.Integer.Type.signumInteger", liftUnary signumInteger)
  , ("GHC.Integer.Type.quotInteger", liftBinary quotInteger)
  , ("GHC.Integer.Type.remInteger", liftBinary remInteger)
--, ("GHC.Integer.Type.quotRemInteger", _)
  , ("GHC.Integer.Type.divInteger", liftBinary divInteger)
  , ("GHC.Integer.Type.modInteger", liftBinary modInteger)
--, ("GHC.Integer.Type.divModInteger", _)

    -- Comparison predicates
  , ("GHC.Integer.Type.gtInteger", liftBinary gtInteger)
  , ("GHC.Integer.Type.geInteger", liftBinary geInteger)
  , ("GHC.Integer.Type.eqInteger", liftBinary eqInteger)
  , ("GHC.Integer.Type.neqInteger", liftBinary neqInteger)
  , ("GHC.Integer.Type.ltInteger", liftBinary ltInteger)
  , ("GHC.Integer.Type.leInteger", liftBinary leInteger)
  , ("GHC.Integer.Type.compareInteger", liftBinary compareInteger)

    -- Int#-boolean valued verisons of comparison predicates
  , ("GHC.Integer.Type.gtInteger#", integerComparison gtInteger#)
  , ("GHC.Integer.Type.geInteger#", integerComparison geInteger#)
  , ("GHC.Integer.Type.eqInteger#", integerComparison eqInteger#)
  , ("GHC.Integer.Type.neqInteger#", integerComparison neqInteger#)
  , ("GHC.Integer.Type.ltInteger#", integerComparison ltInteger#)
  , ("GHC.Integer.Type.leInteger#", integerComparison leInteger#)

    -- Bit-operations
  , ("GHC.Integer.bitInteger", primBitInteger)
  , ("GHC.Integer.Type.andInteger", liftBinary andInteger)
  , ("GHC.Integer.Type.orInteger", liftBinary orInteger)
  , ("GHC.Integer.Type.xorInteger", liftBinary xorInteger)
  , ("GHC.Integer.Type.complementInteger", liftUnary complementInteger)
  , ("GHC.Integer.Type.shiftLInteger", primShiftLInteger)
  , ("GHC.Integer.Type.shiftRInteger", primShiftRInteger)
  , ("GHC.Integer.Type.testBitInteger", primTestBitInteger)

    -- Hashing
  , ("GHC.Integer.Type.hashInteger", primHashInteger)
  ]

primIntegerLogBase :: PrimImpl
primIntegerLogBase =
  liftBinary $ \x y -> toInteger $ I# (integerLogBase# x y)

primSmallInteger :: PrimImpl
primSmallInteger =
  liftUnary $ \x ->
    let !(I# a) = x in smallInteger a

primWordToInteger :: PrimImpl
primWordToInteger =
  liftUnary $ \x ->
    let !(W# a) = x in wordToInteger a

primIntegerToWord :: PrimImpl
primIntegerToWord =
  liftUnary $ \x -> W# (integerToWord x)

primIntegerToInt :: PrimImpl
primIntegerToInt =
  liftUnary $ \x -> I# (integerToInt x)

primEncodeFloatInteger :: PrimImpl
primEncodeFloatInteger =
  liftBinary $ \x y ->
    let !(I# a) = y in F# (encodeFloatInteger x a)

primFloatFromInteger :: PrimImpl
primFloatFromInteger =
  liftUnary $ \x -> F# (floatFromInteger x)

primEncodeDoubleInteger :: PrimImpl
primEncodeDoubleInteger =
  liftBinary $ \x y ->
    let !(I# a) = y in D# (encodeDoubleInteger x a)

primDoubleFromInteger :: PrimImpl
primDoubleFromInteger =
  liftUnary $ \x -> D# (doubleFromInteger x)

primBitInteger :: PrimImpl
primBitInteger =
  liftUnary $ \x ->
    let !(I# a) = x in bitInteger a

primShiftLInteger :: PrimImpl
primShiftLInteger =
  liftBinary $ \x y ->
    let !(I# a) = y in shiftLInteger x a

primShiftRInteger :: PrimImpl
primShiftRInteger =
  liftBinary $ \x y ->
    let !(I# a) = y in shiftRInteger x a

primTestBitInteger :: PrimImpl
primTestBitInteger =
  liftBinary $ \x y ->
    let !(I# a) = y in testBitInteger x a

primHashInteger :: PrimImpl
primHashInteger =
  liftUnary $ \i -> I# (hashInteger i)

integerComparison :: (Integer -> Integer -> Int#) -> PrimImpl
integerComparison op =
  liftBinary (\x y -> I# (x `op` y))

