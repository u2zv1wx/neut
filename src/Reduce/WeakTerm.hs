module Reduce.WeakTerm
  ( reduceWeakTermPlus
  ) where

import Data.Bits
import Data.Fixed (mod')
import Numeric.Half
import Unsafe.Coerce -- for int -> word, word -> int

import Data.Basic
import Data.Env
import Data.WeakTerm

reduceWeakTermPlus :: WeakTermPlus -> WithEnv WeakTermPlus
reduceWeakTermPlus (m, WeakTermEpsilonElim e branchList) = do
  e' <- reduceWeakTermPlus e
  case e' of
    (_, WeakTermEpsilonIntro l) ->
      case lookup (CaseLabel l) branchList of
        Just body -> reduceWeakTermPlus body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceWeakTermPlus body
            Nothing -> return (m, WeakTermEpsilonElim e' branchList)
    _ -> return (m, WeakTermEpsilonElim e' branchList)
reduceWeakTermPlus (m, WeakTermPiElim e es) = do
  e' <- reduceWeakTermPlus e
  es' <- mapM reduceWeakTermPlus es
  let app = WeakTermPiElim e' es'
  case e' of
    (_, WeakTermPiIntro xts body)
      | length xts == length es'
      , all isValue es' -> do
        let xs = map fst xts
        reduceWeakTermPlus $ substWeakTermPlus (zip xs es') body
    self@(_, WeakTermMu (x, _) body)
      | all isValue es' -> do
        let self' = substWeakTermPlus [(x, self)] body
        reduceWeakTermPlus (m, WeakTermPiElim self' es')
    (_, WeakTermTheta constant) ->
      reduceWeakTermPlusTheta (m, app) es' m constant
    _ -> return (m, app)
reduceWeakTermPlus t = return t

reduceWeakTermPlusTheta ::
     WeakTermPlus
  -> [WeakTermPlus]
  -> WeakMeta
  -> Identifier
  -> WithEnv WeakTermPlus
reduceWeakTermPlusTheta orig es m constant
  | Just (lowType, op) <- asUnaryOpMaybe constant
  , [arg] <- es = reduceWeakTermPlusUnary orig arg m lowType op
  | Just (lowType, op) <- asBinaryOpMaybe constant
  , [arg1, arg2] <- es = reduceWeakTermPlusBinary orig arg1 arg2 m lowType op
  | otherwise = return orig

reduceWeakTermPlusUnary ::
     WeakTermPlus
  -> WeakTermPlus
  -> WeakMeta
  -> LowType
  -> UnaryOp
  -> WithEnv WeakTermPlus
reduceWeakTermPlusUnary orig arg _ lowType _ = do
  case getUnaryArgInfo lowType arg of
    Just (UnaryArgInfoIntS _ _) -> undefined
    Just (UnaryArgInfoIntU _ _) -> undefined
    Just (UnaryArgInfoFloat16 _) -> undefined
    Just (UnaryArgInfoFloat32 _) -> undefined
    Just (UnaryArgInfoFloat64 _) -> undefined
    Nothing -> return orig
  -- case op of
  --   UnaryOpNeg -> undefined
  --   UnaryOpTrunc _ -> undefined
  --   UnaryOpZext _ -> undefined
  --   UnaryOpSext _ -> undefined
  --   UnaryOpFpExt _ -> undefined
  --   UnaryOpTo _ -> undefined
  --   _ -> return orig
    -- (_, WeakTermTheta constant)
    --   | [(_, WeakTermInt x)] <- es'
    --   , Just (LowTypeSignedInt _, op) <- asUnaryOpMaybe constant -> do
    --     case op of
    --       UnaryOpTrunc _ -> undefined
    --       UnaryOpZext _ -> return (m, WeakTermInt x)
    --       UnaryOpSext _ -> undefined
    --       UnaryOpTo (LowTypeFloat _) ->
    --         return (m, WeakTermFloat64 (fromIntegral x))
    --       _ -> return (m, app)
    -- (_, WeakTermTheta constant)
    --   | [(_, WeakTermInt x)] <- es'
    --   , Just (LowTypeUnsignedInt _, op) <- asUnaryOpMaybe constant -> do
    --     case op of
    --       UnaryOpTrunc _ -> undefined
    --       UnaryOpZext _ -> return (m, WeakTermInt x)
    --       UnaryOpSext _ -> undefined
    --       UnaryOpTo (LowTypeFloat _) ->
    --         return (m, WeakTermFloat64 (fromIntegral x))
    --       _ -> return (m, app)
    -- (_, WeakTermTheta constant)
    --   | [(_, WeakTermFloat64 x)] <- es'
    --   , Just (LowTypeFloat _, op) <- asUnaryOpMaybe constant ->
    --     case op of
    --       UnaryOpNeg -> return (m, WeakTermFloat64 (-x))
    --       UnaryOpTrunc _ -> undefined
    --       UnaryOpFpExt _ -> undefined
    --       UnaryOpTo _ -> undefined
    --       _ -> return (m, app)

reduceWeakTermPlusBinary ::
     WeakTermPlus
  -> WeakTermPlus
  -> WeakTermPlus
  -> WeakMeta
  -> LowType
  -> BinaryOp
  -> WithEnv WeakTermPlus
reduceWeakTermPlusBinary orig arg1 arg2 m lowType op = do
  case getBinaryArgInfo lowType arg1 arg2 of
    Just (BinaryArgInfoIntS size x y) ->
      asWeakTermPlus m (computeIntS x y op) (WeakTermIntS size)
    Just (BinaryArgInfoIntU size x y) ->
      asWeakTermPlus m (computeIntU x y op) (WeakTermIntU size)
    Just (BinaryArgInfoFloat16 x y) ->
      asWeakTermPlus m (computeFloat x y op (snd orig)) WeakTermFloat16
    Just (BinaryArgInfoFloat32 x y) ->
      asWeakTermPlus m (computeFloat x y op (snd orig)) WeakTermFloat32
    Just (BinaryArgInfoFloat64 x y) ->
      asWeakTermPlus m (computeFloat x y op (snd orig)) WeakTermFloat64
    Nothing -> return orig

asWeakTermPlus :: Monad m => a -> Either b t -> (t -> b) -> m (a, b)
asWeakTermPlus m boolOrCalcResult f =
  case boolOrCalcResult of
    Left b -> return (m, b)
    Right i -> return (m, f i)

data UnaryArgInfo
  = UnaryArgInfoIntS IntSize Integer
  | UnaryArgInfoIntU IntSize Integer
  | UnaryArgInfoFloat16 Half
  | UnaryArgInfoFloat32 Float
  | UnaryArgInfoFloat64 Double
  deriving (Show, Eq)

getUnaryArgInfo :: LowType -> WeakTermPlus -> Maybe UnaryArgInfo
-- IntS
getUnaryArgInfo (LowTypeSignedInt s) (_, WeakTermIntS s1 x)
  | s == s1 = return $ UnaryArgInfoIntS s x
-- IntU
getUnaryArgInfo (LowTypeUnsignedInt s) (_, WeakTermIntU s1 x)
  | s == s1 = return $ UnaryArgInfoIntU s x
-- Int with size specified by lowType
getUnaryArgInfo (LowTypeSignedInt s) (_, WeakTermInt x) =
  return $ UnaryArgInfoIntS s x
-- Float16
getUnaryArgInfo (LowTypeFloat FloatSize16) (_, WeakTermFloat16 x) =
  return $ UnaryArgInfoFloat16 x
-- Float32
getUnaryArgInfo (LowTypeFloat FloatSize32) (_, WeakTermFloat32 x) =
  return $ UnaryArgInfoFloat32 x
-- Float64
getUnaryArgInfo (LowTypeFloat FloatSize64) (_, WeakTermFloat64 x) =
  return $ UnaryArgInfoFloat64 x
-- Float with size specified by lowType
getUnaryArgInfo (LowTypeFloat FloatSize16) (_, WeakTermFloat x) =
  return $ UnaryArgInfoFloat16 (realToFrac x)
getUnaryArgInfo (LowTypeFloat FloatSize32) (_, WeakTermFloat x) =
  return $ UnaryArgInfoFloat32 (realToFrac x)
getUnaryArgInfo (LowTypeFloat FloatSize64) (_, WeakTermFloat x) =
  return $ UnaryArgInfoFloat64 (realToFrac x)
-- otherwise (invalid argument)
getUnaryArgInfo _ _ = Nothing

data BinaryArgInfo
  = BinaryArgInfoIntS IntSize Integer Integer
  | BinaryArgInfoIntU IntSize Integer Integer
  | BinaryArgInfoFloat16 Half Half
  | BinaryArgInfoFloat32 Float Float
  | BinaryArgInfoFloat64 Double Double
  deriving (Show, Eq)

getBinaryArgInfo ::
     LowType -> WeakTermPlus -> WeakTermPlus -> Maybe BinaryArgInfo
-- IntS
getBinaryArgInfo (LowTypeSignedInt s) (_, WeakTermIntS s1 x) (_, WeakTermIntS s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeSignedInt s) (_, WeakTermInt x) (_, WeakTermIntS s2 y)
  | s == s2 = return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeSignedInt s) (_, WeakTermIntS s1 x) (_, WeakTermInt y)
  | s == s1 = return $ BinaryArgInfoIntS s x y
-- IntU
getBinaryArgInfo (LowTypeUnsignedInt s) (_, WeakTermIntU s1 x) (_, WeakTermIntU s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntU s x y
getBinaryArgInfo (LowTypeUnsignedInt s) (_, WeakTermInt x) (_, WeakTermIntU s2 y)
  | s == s2 = return $ BinaryArgInfoIntU s x y
getBinaryArgInfo (LowTypeUnsignedInt s) (_, WeakTermIntU s1 x) (_, WeakTermInt y)
  | s == s1 = return $ BinaryArgInfoIntU s x y
-- Int with size specified by lowType
getBinaryArgInfo (LowTypeSignedInt s) (_, WeakTermInt x) (_, WeakTermInt y) =
  return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeUnsignedInt s) (_, WeakTermInt x) (_, WeakTermInt y) =
  return $ BinaryArgInfoIntU s x y
-- Float16
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, WeakTermFloat16 x) (_, WeakTermFloat16 y) =
  return $ BinaryArgInfoFloat16 x y
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, WeakTermFloat x) (_, WeakTermFloat16 y) =
  return $ BinaryArgInfoFloat16 (realToFrac x) y
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, WeakTermFloat16 x) (_, WeakTermFloat y) =
  return $ BinaryArgInfoFloat16 x (realToFrac y)
-- Float32
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, WeakTermFloat32 x) (_, WeakTermFloat32 y) =
  return $ BinaryArgInfoFloat32 x y
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, WeakTermFloat x) (_, WeakTermFloat32 y) =
  return $ BinaryArgInfoFloat32 (realToFrac x) y
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, WeakTermFloat32 x) (_, WeakTermFloat y) =
  return $ BinaryArgInfoFloat32 x (realToFrac y)
-- Float64
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, WeakTermFloat64 x) (_, WeakTermFloat64 y) =
  return $ BinaryArgInfoFloat64 x y
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, WeakTermFloat x) (_, WeakTermFloat64 y) =
  return $ BinaryArgInfoFloat64 (realToFrac x) y
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, WeakTermFloat64 x) (_, WeakTermFloat y) =
  return $ BinaryArgInfoFloat64 x (realToFrac y)
-- Float with size specified by lowType
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, WeakTermFloat x) (_, WeakTermFloat y) =
  return $ BinaryArgInfoFloat16 (realToFrac x) (realToFrac y)
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, WeakTermFloat x) (_, WeakTermFloat y) =
  return $ BinaryArgInfoFloat32 (realToFrac x) (realToFrac y)
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, WeakTermFloat x) (_, WeakTermFloat y) =
  return $ BinaryArgInfoFloat64 x y
-- otherwise (invalid arguments)
getBinaryArgInfo _ _ _ = Nothing

computeIntS :: (Integral a, Bits a) => a -> a -> BinaryOp -> Either WeakTerm a
computeIntS = undefined

computeIntU :: (Integral a, Bits a) => a -> a -> BinaryOp -> Either WeakTerm a
computeIntU = undefined

computeInt :: (Integral a, Bits a) => a -> a -> BinaryOp -> Either WeakTerm a
computeInt x y BinaryOpAdd = Right $ x + y
computeInt x y BinaryOpSub = Right $ x - y
computeInt x y BinaryOpMul = Right $ x * y
computeInt x y BinaryOpDiv = Right $ x `div` y
computeInt x y BinaryOpRem = Right $ x `rem` y
computeInt x y BinaryOpEQ = Left $ asEpsilon $ x == y
computeInt x y BinaryOpNE = Left $ asEpsilon $ x /= y
computeInt x y BinaryOpGT = Left $ asEpsilon $ x > y
computeInt x y BinaryOpGE = Left $ asEpsilon $ x >= y
computeInt x y BinaryOpLT = Left $ asEpsilon $ x < y
computeInt x y BinaryOpLE = Left $ asEpsilon $ x <= y
computeInt x y BinaryOpShl = Right $ shiftL x (unsafeCoerce y)
computeInt x y BinaryOpLshr = Right $ ushiftR' x (unsafeCoerce y)
computeInt x y BinaryOpAshr = Right $ shiftR x (unsafeCoerce y)
computeInt x y BinaryOpAnd = Right $ x .&. y
computeInt x y BinaryOpOr = Right $ x .|. y
computeInt x y BinaryOpXor = Right $ x `xor` y

computeFloat ::
     (Real a, Fractional a)
  => a
  -> a
  -> BinaryOp
  -> WeakTerm
  -> Either WeakTerm a
computeFloat x y BinaryOpAdd _ = Right $ x + y
computeFloat x y BinaryOpSub _ = Right $ x - y
computeFloat x y BinaryOpMul _ = Right $ x * y
computeFloat x y BinaryOpDiv _ = Right $ x / y
computeFloat x y BinaryOpRem _ = Right $ x `mod'` y
computeFloat x y BinaryOpEQ _ = Left $ asEpsilon $ x == y
computeFloat x y BinaryOpNE _ = Left $ asEpsilon $ x /= y
computeFloat x y BinaryOpGT _ = Left $ asEpsilon $ x > y
computeFloat x y BinaryOpGE _ = Left $ asEpsilon $ x >= y
computeFloat x y BinaryOpLT _ = Left $ asEpsilon $ x < y
computeFloat x y BinaryOpLE _ = Left $ asEpsilon $ x <= y
computeFloat _ _ _ e = Left e

asEpsilon :: Bool -> WeakTerm
asEpsilon True = WeakTermEpsilonIntro "true"
asEpsilon False = WeakTermEpsilonIntro "false"
