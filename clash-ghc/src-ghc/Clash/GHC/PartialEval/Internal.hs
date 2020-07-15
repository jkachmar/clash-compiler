{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}

module Clash.GHC.PartialEval.Internal where

import Control.Applicative (Alternative(..))
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Except (runExcept)
import Control.Monad.Trans.Maybe (MaybeT(..))
import Data.Bitraversable (bitraverse)
import Data.Either (lefts)
import qualified Data.Kind as K
import Data.Primitive.ByteArray (ByteArray(..))
import Data.Proxy
import Data.Reflection (reifyNat)
import GHC.Int
import GHC.Integer.GMP.Internals (Integer(..), BigNat(..))
import GHC.Natural (Natural(..), naturalFromInteger, naturalToInteger)
import GHC.TypeLits
import GHC.Types hiding (Type)

import Clash.Sized.Internal.BitVector
import Clash.Sized.Internal.Index
import Clash.Sized.Internal.Signed
import Clash.Sized.Internal.Unsigned

import Clash.Core.DataCon
import Clash.Core.Evaluator.Models
import Clash.Core.Literal
import Clash.Core.Term
import Clash.Core.TyCon
import Clash.Core.Type
import Clash.Core.TysPrim
import Clash.Core.Util (tyNatSize)
import Clash.Unique

type PrimEval = MaybeT Eval
type PrimImpl = Evaluator -> PrimInfo -> [Either Term Type] -> PrimEval Value

-- | Evaluate a primitive to obtain some value. If the primitive cannot be
-- evaluated, the supplied action is used to generate a default value.
--
runPrimEval :: PrimEval a -> Eval a -> Eval a
runPrimEval (MaybeT m) x = m >>= maybe x pure

-- | The primitive is already a value, and is repackaged as NePrim after its
-- arguments are evaluated.
--
liftId :: PrimImpl
liftId e p args = do
  vals <- lift $ traverse (bitraverse (evaluateWhnf e) pure) args
  pure (VNeu (NePrim p vals))

-- | Lift a unary function to an implemenatation for a primitive operation.
-- This is used for primitives where the evaluation does not differ from the
-- semantics of the underlying Haskell implemenatation.
--
liftUnary :: (FromAst a, ToAst b) => (a -> b) -> PrimImpl
liftUnary f e p args
  | [x] <- lefts args
  = do a <- fromTermOrValue e x
       toValue (f a) (primType p)

  | otherwise
  = empty

-- | Lift a binary function to an implementation for a primitive operation.
-- See liftUnary for more information.
--
liftBinary
  :: (FromAst a, FromAst b, ToAst c)
  => (a -> b -> c)
  -> PrimImpl
liftBinary f e p args
  | [x, y] <- lefts args
  = do a <- fromTermOrValue e x
       b <- fromTermOrValue e y
       toValue (f a b) (primType p)

  | otherwise
  = empty

-- | Lift a constructor for a boxed type, e.g. I# for Int. Attempting to use
-- this function on other constructors may fail as it expects a unary
-- constructor.
--
liftBox
  :: (FromAst a)
  => (LocalEnv -> DataCon -> a -> Value)
  -> PrimImpl
liftBox f e p args = do
  env <- lift getLocalEnv
  [boxDc] <- typeDcs (primType p)
  liftUnary (f env boxDc) e p args

liftUnarySized
  :: forall (f :: Nat -> K.Type) (n :: Nat) (m :: Nat)
   . (FromAst (Sized (f n)), ToAst (Sized (f m)))
  => (Integer -> Integer)
  -> (f n -> f m)
  -> PrimImpl
liftUnarySized szF f e p args
  | [x] <- lefts args
  = do Sized sz a <- fromTermOrValue e x :: PrimEval (Sized (f n))
       let b = reifyNat sz (\Proxy -> f) a

       toValue @(Sized (f m)) (Sized (szF sz) b) (primType p)

  | otherwise
  = error "liftUnarySized"

liftBinarySized
  :: forall (f :: Nat -> K.Type) (n :: Nat) (m :: Nat) (l :: Nat)
   . ( KnownNat n, KnownNat m, KnownNat l
     , FromAst (Sized (f n)), FromAst (Sized (f m)), ToAst (Sized (f l))
     )
  => (Integer -> Integer -> Integer)
  -> (f n -> f m -> f l)
  -> PrimImpl
liftBinarySized szF f e p args
  | [x, y] <- lefts args
  = do Sized szA a <- fromTermOrValue e x :: PrimEval (Sized (f n))
       Sized szB b <- fromTermOrValue e y :: PrimEval (Sized (f m))

       toValue @(Sized (f l)) (Sized (szF szA szB) (f a b)) (primType p)

  | otherwise
  = empty

-- | Type constructor name, args, data constructors.
--
typeInfo :: Type -> PrimEval (TyConName, [Type], [DataCon])
typeInfo ty
  | TyConApp tcNm args <- tyView $ snd (splitFunForallTy ty)
  = do tcm <- lift getTyConMap
       tc <- MaybeT $ pure (lookupUniqMap tcNm tcm)

       pure (tcNm, args, tyConDataCons tc)

  | otherwise
  = error "typeInfo: Not a TyConApp"

typeArgsDcs :: Type -> PrimEval ([Type], [DataCon])
typeArgsDcs = fmap (\(_, tys, dcs) -> (tys, dcs)) . typeInfo

typeDcs :: Type -> PrimEval [DataCon]
typeDcs = fmap (\(_, _, dcs) -> dcs) . typeInfo

typeSize :: Type -> PrimEval Integer
typeSize ty = do
  tcm <- lift getTyConMap
  either (const empty) pure $ runExcept (tyNatSize tcm ty)

-- A value of some sized type, e.g. BitVector, with it's statically known size.
-- This size can be used with reifyNat to call primtiives with KnownNat
-- constraints.
--
data Sized a = Sized
  { sizedNat :: Integer
  , sizedVal :: a
  } deriving (Functor)

-- | Attempt to inspect an argument, evaluating it if necessary.
--
fromTermOrValue :: (FromAst a) => Evaluator -> Term -> PrimEval a
fromTermOrValue e x = fromTerm x <|> (lift (evaluateWhnf e x) >>= fromValue)

-- | FromAst gets value of a given type from some representation of an AST.
-- Failure means that the AST does not represent the value directly, but some
-- computation that returns a value of the desired type.
--
-- Extracting from Term or Value means primitives can be implemented lazily.
-- Consider the Term AST for
--
--   True && (let ... in False)
--
-- Initially, fromTerm can be used to potentially extract a value without
-- evaluating the term. This works for the LHS of (&&), but not the RHS.
-- However, if the RHS is evaluated, then fromValue will yield the False,
-- allowing the primitive (&&) to be evaluated. With judicial use of evaluate,
-- primitives can be implemented as lazy in all indeterminable arguments.
--
class FromAst a where
  fromTerm  :: Term -> PrimEval a
  fromValue :: Value -> PrimEval a

instance FromAst ByteArray where
  fromTerm = \case
    Literal (ByteArrayLiteral ba) -> pure ba
    _ -> empty

  fromValue = \case
    VLit (ByteArrayLiteral ba) -> pure ba
    _ -> empty

instance FromAst Char where
  fromTerm = \case
    Literal (CharLiteral c) -> pure c
    _ -> empty

  fromValue = \case
    VLit (CharLiteral c) -> pure c
    _ -> empty

instance FromAst Integer where
  fromTerm = \case
    Literal (IntegerLiteral x) -> pure x

    Data dc `App` x
      | dcTag dc == 1 -> do
          I# i <- fromTerm x
          pure (S# i)

      | dcTag dc == 2 -> do
          ByteArray ba <- fromTerm x
          pure (Jp# (BN# ba))

      | dcTag dc == 3 -> do
          ByteArray ba <- fromTerm x
          pure (Jn# (BN# ba))

    _ -> empty

  fromValue = \case
    VLit (IntegerLiteral x) -> pure x

    VData dc [Left x] _env
      | dcTag dc == 1 -> do
          I# i <- fromTerm x
          pure (S# i)

      | dcTag dc == 2 -> do
          ByteArray ba <- fromTerm x
          pure (Jp# (BN# ba))

      | dcTag dc == 3 -> do
          ByteArray ba <- fromTerm x
          pure (Jn# (BN# ba))

    _ -> empty

instance FromAst Int where
  fromTerm = \case
    Literal (IntLiteral x) -> pure (fromInteger x)
    _ -> empty

  fromValue = \case
    VLit (IntLiteral x) -> pure (fromInteger x)
    _ -> empty

instance FromAst Natural where
  fromTerm = \case
    Literal (NaturalLiteral x) -> pure (naturalFromInteger x)

    Data dc `App` x
      | dcTag dc == 1 -> do
          W# i <- fromTerm x
          pure (NatS# i)

      | dcTag dc == 2 -> do
          ByteArray ba <- fromTerm x
          pure (NatJ# (BN# ba))

    _ -> empty

  fromValue = \case
    VLit (NaturalLiteral x) -> pure (naturalFromInteger x)

    VData dc [Left x] _env
      | dcTag dc == 1 -> do
          W# i <- fromTerm x
          pure (NatS# i)

      | dcTag dc == 2 -> do
          ByteArray ba <- fromTerm x
          pure (NatJ# (BN# ba))

    _ -> empty

instance FromAst Word where
  fromTerm = \case
    Literal (WordLiteral x) -> pure (fromInteger x)
    _ -> empty

  fromValue = \case
    VLit (WordLiteral x) -> pure (fromInteger x)
    _ -> empty

instance FromAst Float where
  fromTerm = \case
    Literal (FloatLiteral x) -> pure (fromRational x)
    _ -> empty

  fromValue = \case
    VLit (FloatLiteral x) -> pure (fromRational x)
    _ -> empty

instance FromAst Double where
  fromTerm = \case
    Literal (DoubleLiteral x) -> pure (fromRational x)
    _ -> empty

  fromValue = \case
    VLit (DoubleLiteral x) -> pure (fromRational x)
    _ -> empty

instance FromAst Bit where
  fromTerm term
    | Prim p `App` m `App` i <- term
    , primName p == "Clash.Sized.Internal.BitVector.fromInteger##"
    = Bit <$> fromTerm m <*> fromTerm i

    | otherwise
    = error "fromTerm: Bit"

  fromValue val
    | VPrim p [Left m, Left i] _env <- val
    , primName p == "Clash.Sized.Internal.BitVector.fromInteger##"
    = Bit <$> fromTerm m <*> fromTerm i

    | otherwise
    = error "fromValue: Bit"

instance FromAst (Sized (BitVector n)) where
  fromTerm term
    | Prim p `TyApp` n `App` m `App` i <- term
    , primName p == "Clash.Sized.Internal.BitVector.fromInteger#"
    = do sz <- typeSize n
         bv <- BV <$> fromTerm m <*> fromTerm i

         pure (Sized sz bv)

    | otherwise
    = error "fromTerm: BitVector"

  fromValue val
    | VPrim p [Right n, Left m, Left i] _env <- val
    , primName p == "Clash.Sized.Internal.BitVector.fromInteger#"
    = do sz <- typeSize n
         bv <- BV <$> fromTerm m <*> fromTerm i

         pure (Sized sz bv)

    | otherwise
    = error "fromValue: BitVector"

instance FromAst (Sized (Index n)) where
  fromTerm term
    | Prim p `TyApp` n `App` i <- term
    , primName p == "Clash.Sized.Internal.Index.fromInteger#"
    = do sz <- typeSize n
         ix <- I <$> fromTerm i

         pure (Sized sz ix)

    | otherwise
    = error "fromTerm: Index"

  fromValue val
    | VPrim p [Right n, Left i] _env <- val
    , primName p == "Clash.Sized.Internal.Index.fromInteger#"
    = do sz <- typeSize n
         ix <- I <$> fromTerm i

         pure (Sized sz ix)

    | otherwise
    = error "fromValue: Index"

instance FromAst (Sized (Signed n)) where
  fromTerm term
    | Prim p `TyApp` n `App` i <- term
    , primName p == "Clash.Sized.Internal.Signed.fromInteger#"
    = do sz <- typeSize n
         sn <- S <$> fromTerm i

         pure (Sized sz sn)

    | otherwise
    = error "fromTerm: Signed"

  fromValue val
    | VPrim p [Right n, Left i] _env <- val
    , primName p == "Clash.Sized.Internal.Signed.fromInteger#"
    = do sz <- typeSize n
         sn <- S <$> fromTerm i

         pure (Sized sz sn)

    | otherwise
    = error "fromValue: Signed"

instance FromAst (Sized (Unsigned n)) where
  fromTerm term
    | Prim p `TyApp` n `App` i <- term
    , primName p == "Clash.Sized.Internal.Unsigned.fromInteger#"
    = do sz <- typeSize n
         un <- U <$> fromTerm i

         pure (Sized sz un)

    | otherwise
    = error "fromTerm: Unsigned"

  fromValue val
    | VPrim p [Right n, Left i] _env <- val
    , primName p == "Clash.Sized.Internal.Unsigned.fromInteger#"
    = do sz <- typeSize n
         un <- U <$> fromTerm i

         pure (Sized sz un)

    | otherwise
    = error "fromValue: Unsigned"

-- | When evaluating a primitive, the result needs to be converted back into
-- a Value. As evaluation only returns Value (and not Term) there is not a
-- toTerm function in this class.
--
class ToAst a where
  toTerm  :: a -> Type -> PrimEval Term
  toValue :: a -> Type -> PrimEval Value

instance ToAst Bool where
  toTerm b ty = do
    [falseDc, trueDc] <- typeDcs ty
    pure (Data (if b then trueDc else falseDc))

  toValue b ty = do
    env <- lift getLocalEnv
    [falseDc, trueDc] <- typeDcs ty

    pure (VData (if b then trueDc else falseDc) [] env)

instance ToAst ByteArray where
  toTerm  = const . pure . Literal . ByteArrayLiteral
  toValue = const . pure . VLit . ByteArrayLiteral

instance ToAst Char where
  toTerm  = const . pure . Literal . CharLiteral
  toValue = const . pure . VLit . CharLiteral

instance ToAst Integer where
  toTerm  = const . pure . Literal . IntegerLiteral
  toValue = const . pure . VLit . IntegerLiteral

instance ToAst Int where
  toTerm  = const . pure . Literal . IntLiteral . toInteger
  toValue = const . pure . VLit . IntLiteral . toInteger

instance ToAst Int64 where
  toTerm  = const . pure . Literal . IntLiteral . toInteger
  toValue = const . pure . VLit . IntLiteral . toInteger

instance ToAst Natural where
  toTerm  = const . pure . Literal . NaturalLiteral . naturalToInteger
  toValue = const . pure . VLit . NaturalLiteral . naturalToInteger

instance ToAst Word where
  toTerm  = const . pure . Literal . WordLiteral . toInteger
  toValue = const . pure . VLit . WordLiteral . toInteger

instance ToAst Float where
  toTerm  = const . pure . Literal . FloatLiteral . toRational
  toValue = const . pure . VLit . FloatLiteral . toRational

instance ToAst Double where
  toTerm  = const . pure . Literal . DoubleLiteral . toRational
  toValue = const . pure . VLit . DoubleLiteral . toRational

instance ToAst Ordering where
  toTerm x ty = do
    [ltDc, eqDc, gtDc] <- typeDcs ty

    case x of
      LT -> pure (Data ltDc)
      EQ -> pure (Data eqDc)
      GT -> pure (Data gtDc)

  toValue x ty = do
    env <- lift getLocalEnv
    [ltDc, eqDc, gtDc] <- typeDcs ty

    case x of
      LT -> pure (VData ltDc [] env)
      EQ -> pure (VData eqDc [] env)
      GT -> pure (VData gtDc [] env)

instance ToAst Value where
  toTerm  = const . pure . asTerm
  toValue = const . pure

instance (ToAst a, ToAst b) => ToAst (a, b) where
  toTerm (a, b) ty = do
    ([aTy, bTy], [tupDc]) <- typeArgsDcs ty
    a' <- toTerm a aTy
    b' <- toTerm b bTy

    pure (mkApps (Data tupDc) [Right aTy, Right bTy, Left a', Left b'])

  toValue (a, b) ty = do
    env <- lift getLocalEnv
    ([aTy, bTy], [tupDc]) <- typeArgsDcs ty
    a' <- toTerm a aTy
    b' <- toTerm b bTy

    pure (VData tupDc [Right aTy, Right bTy, Left a', Left b'] env)

instance (ToAst a, ToAst b, ToAst c, ToAst d) => ToAst (a, b, c, d) where
  toTerm (a, b, c, d) ty = do
    ([aTy, bTy, cTy, dTy], [tupDc]) <- typeArgsDcs ty
    a' <- toTerm a aTy
    b' <- toTerm b bTy
    c' <- toTerm c cTy
    d' <- toTerm d dTy

    pure $ mkApps (Data tupDc)
      [ Right aTy, Right bTy, Right cTy, Right dTy
      , Left a', Left b', Left c', Left d'
      ]

  toValue (a, b, c, d) ty = do
    env <- lift getLocalEnv
    ([aTy, bTy, cTy, dTy], [tupDc]) <- typeArgsDcs ty
    a' <- toTerm a aTy
    b' <- toTerm b bTy
    c' <- toTerm c cTy
    d' <- toTerm d dTy

    pure $ flip (VData tupDc) env
      [ Right aTy, Right bTy, Right cTy, Right dTy
      , Left a', Left b', Left c', Left d'
      ]

mkPrimBit :: Type -> PrimEval PrimInfo
mkPrimBit ty = do
  (bNm, args, _) <- typeInfo ty
  let pTy = foldr1 mkFunTy [wordPrimTy, integerPrimTy, mkTyConApp bNm args]

  pure $ PrimInfo
    { primName = "Clash.Sized.Internal.BitVector.fromInteger##"
    , primType = pTy
    , primWorkInfo = WorkNever
    }

instance ToAst Bit where
  toTerm (Bit m i) ty = do
    p <- mkPrimBit ty
    m' <- toTerm m integerPrimTy
    i' <- toTerm i integerPrimTy

    pure $ mkApps (Prim p) [Left m', Left i']

  toValue (Bit m i) ty = do
    env <- lift getLocalEnv
    p <- mkPrimBit ty
    m' <- toTerm m integerPrimTy
    i' <- toTerm i integerPrimTy

    pure (VPrim p [Left m', Left i'] env)

mkPrimBV :: Type -> PrimEval PrimInfo
mkPrimBV ty = do
  (bvNm, [VarTy n], _) <- typeInfo ty
  let pTy = mkPolyFunTy (mkTyConApp bvNm [VarTy n])
              [Left n, Right naturalPrimTy, Right naturalPrimTy]

  pure $ PrimInfo
    { primName = "Clash.Sized.Internal.BitVector.fromInteger#"
    , primType = pTy
    , primWorkInfo = WorkNever
    }

instance ToAst (Sized (BitVector n)) where
  toTerm (Sized n (BV m i)) ty = do
    p <- mkPrimBV ty
    let n' = LitTy (NumTy n)
    m' <- toTerm m integerPrimTy
    i' <- toTerm i integerPrimTy

    pure $ mkApps (Prim p) [Right n', Left m', Left i']

  toValue (Sized n (BV m i)) ty = do
    env <- lift getLocalEnv
    p <- mkPrimBV ty
    let n' = LitTy (NumTy n)
    m' <- toTerm m integerPrimTy
    i' <- toTerm i integerPrimTy

    pure (VPrim p [Right n', Left m', Left i'] env)

mkPrimIndex :: Type -> PrimEval PrimInfo
mkPrimIndex ty = do
  (iNm, [VarTy n], _) <- typeInfo ty
  let pTy = mkPolyFunTy (mkTyConApp iNm [VarTy n])
              [Left n, Right integerPrimTy]

  pure $ PrimInfo
    { primName = "Clash.Sized.Internal.Index.fromInteger#"
    , primType = pTy
    , primWorkInfo = WorkNever
    }

instance ToAst (Sized (Index n)) where
  toTerm (Sized n (I i)) ty = do
    p <- mkPrimIndex ty
    let n' = LitTy (NumTy n)
    i' <- toTerm i integerPrimTy

    pure $ mkApps (Prim p) [Right n', Left i']

  toValue (Sized n (I i)) ty = do
    env <- lift getLocalEnv
    p <- mkPrimIndex ty
    let n' = LitTy (NumTy n)
    i' <- toTerm i integerPrimTy

    pure $ VPrim p [Right n', Left i'] env

mkPrimSigned :: Type -> PrimEval PrimInfo
mkPrimSigned ty = do
  (sNm, [VarTy n], _) <- typeInfo ty
  let pTy = mkPolyFunTy (mkTyConApp sNm [VarTy n])
              [Left n, Right integerPrimTy]

  pure $ PrimInfo
    { primName = "Clash.Sized.Internal.Signed.fromInteger#"
    , primType = pTy
    , primWorkInfo = WorkNever
    }

instance ToAst (Sized (Signed n)) where
  toTerm (Sized n (S i)) ty = do
    p <- mkPrimSigned ty
    let n' = LitTy (NumTy n)
    i' <- toTerm i integerPrimTy

    pure $ mkApps (Prim p) [Right n', Left i']

  toValue (Sized n (S i)) ty = do
    env <- lift getLocalEnv
    p <- mkPrimSigned ty
    let n' = LitTy (NumTy n)
    i' <- toTerm i integerPrimTy

    pure $ VPrim p [Right n', Left i'] env

mkPrimUnsigned :: Type -> PrimEval PrimInfo
mkPrimUnsigned ty = do
  (uNm, [VarTy n], _) <- typeInfo ty
  let pTy = mkPolyFunTy (mkTyConApp uNm [VarTy n])
              [Left n, Right integerPrimTy]

  pure $ PrimInfo
    { primName = "Clash.Sized.Internal.Unsigned.fromInteger#"
    , primType = pTy
    , primWorkInfo = WorkNever
    }

instance ToAst (Sized (Unsigned n)) where
  toTerm (Sized n (U i)) ty = do
    p <- mkPrimUnsigned ty
    let n' = LitTy (NumTy n)
    i' <- toTerm i integerPrimTy

    pure $ mkApps (Prim p) [Right n', Left i']

  toValue (Sized n (U i)) ty = do
    env <- lift getLocalEnv
    p <- mkPrimUnsigned ty
    let n' = LitTy (NumTy n)
    i' <- toTerm i integerPrimTy

    pure $ VPrim p [Right n', Left i'] env

