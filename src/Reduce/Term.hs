module Reduce.Term
  ( reduceTermPlus
  ) where

import Data.Bits
import Data.Fixed (mod')
import Numeric.Half
import Unsafe.Coerce -- for int -> word, word -> int

import Data.Basic
import Data.Env
import Data.Term

reduceTermPlus :: TermPlus -> WithEnv TermPlus
reduceTermPlus (m, TermEpsilonElim e branchList) = do
  e' <- reduceTermPlus e
  case e' of
    (_, TermEpsilonIntro l) ->
      case lookup (CaseLabel l) branchList of
        Just body -> reduceTermPlus body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceTermPlus body
            Nothing -> return (m, TermEpsilonElim e' branchList)
    _ -> return (m, TermEpsilonElim e' branchList)
reduceTermPlus (m, TermPiElim e es) = do
  e' <- reduceTermPlus e
  es' <- mapM reduceTermPlus es
  let app = TermPiElim e' es'
  case e' of
    (_, TermPiIntro xts body)
      | length xts == length es'
      , all isValue es' -> do
        let xs = map fst xts
        reduceTermPlus $ substTermPlus (zip xs es') body
    self@(_, TermMu (x, _) body)
      | all isValue es' -> do
        let self' = substTermPlus [(x, self)] body
        reduceTermPlus (m, TermPiElim self' es')
    (_, TermTheta constant) -> reduceTermPlusTheta (m, app) es' m constant
    _ -> return (m, app)
reduceTermPlus t = return t

reduceTermPlusTheta ::
     TermPlus -> [TermPlus] -> Meta -> Identifier -> WithEnv TermPlus
reduceTermPlusTheta orig es m constant
  | Just (lowType, op) <- asUnaryOpMaybe constant
  , [arg] <- es = reduceTermPlusUnary orig arg m lowType op
  | Just (lowType, op) <- asBinaryOpMaybe constant
  , [arg1, arg2] <- es = reduceTermPlusBinary orig arg1 arg2 m lowType op
  | otherwise = return orig

reduceTermPlusUnary ::
     TermPlus -> TermPlus -> Meta -> LowType -> UnaryOp -> WithEnv TermPlus
reduceTermPlusUnary orig arg _ lowType _ = do
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
    -- (_, TermTheta constant)
    --   | [(_, TermInt x)] <- es'
    --   , Just (LowTypeSignedInt _, op) <- asUnaryOpMaybe constant -> do
    --     case op of
    --       UnaryOpTrunc _ -> undefined
    --       UnaryOpZext _ -> return (m, TermInt x)
    --       UnaryOpSext _ -> undefined
    --       UnaryOpTo (LowTypeFloat _) ->
    --         return (m, TermFloat64 (fromIntegral x))
    --       _ -> return (m, app)
    -- (_, TermTheta constant)
    --   | [(_, TermInt x)] <- es'
    --   , Just (LowTypeUnsignedInt _, op) <- asUnaryOpMaybe constant -> do
    --     case op of
    --       UnaryOpTrunc _ -> undefined
    --       UnaryOpZext _ -> return (m, TermInt x)
    --       UnaryOpSext _ -> undefined
    --       UnaryOpTo (LowTypeFloat _) ->
    --         return (m, TermFloat64 (fromIntegral x))
    --       _ -> return (m, app)
    -- (_, TermTheta constant)
    --   | [(_, TermFloat64 x)] <- es'
    --   , Just (LowTypeFloat _, op) <- asUnaryOpMaybe constant ->
    --     case op of
    --       UnaryOpNeg -> return (m, TermFloat64 (-x))
    --       UnaryOpTrunc _ -> undefined
    --       UnaryOpFpExt _ -> undefined
    --       UnaryOpTo _ -> undefined
    --       _ -> return (m, app)

reduceTermPlusBinary ::
     TermPlus
  -> TermPlus
  -> TermPlus
  -> Meta
  -> LowType
  -> BinaryOp
  -> WithEnv TermPlus
reduceTermPlusBinary orig arg1 arg2 m lowType op = do
  case getBinaryArgInfo lowType arg1 arg2 of
    Just (BinaryArgInfoIntS size x y) -> do
      let s = toInteger size
      asTermPlus m (computeInt asIntS s x y op) (TermIntS size)
    Just (BinaryArgInfoIntU size x y) -> do
      let s = toInteger size
      asTermPlus m (computeInt asIntU s x y op) (TermIntU size)
    Just (BinaryArgInfoFloat16 x y) ->
      asTermPlus m (computeFloat x y op (snd orig)) TermFloat16
    Just (BinaryArgInfoFloat32 x y) ->
      asTermPlus m (computeFloat x y op (snd orig)) TermFloat32
    Just (BinaryArgInfoFloat64 x y) ->
      asTermPlus m (computeFloat x y op (snd orig)) TermFloat64
    Nothing -> return orig

asTermPlus :: Monad m => a -> Either b t -> (t -> b) -> m (a, b)
asTermPlus m boolOrCalcResult f =
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

getUnaryArgInfo :: LowType -> TermPlus -> Maybe UnaryArgInfo
-- IntS
getUnaryArgInfo (LowTypeSignedInt s) (_, TermIntS s1 x)
  | s == s1 = return $ UnaryArgInfoIntS s x
-- IntU
getUnaryArgInfo (LowTypeUnsignedInt s) (_, TermIntU s1 x)
  | s == s1 = return $ UnaryArgInfoIntU s x
-- Float16
getUnaryArgInfo (LowTypeFloat FloatSize16) (_, TermFloat16 x) =
  return $ UnaryArgInfoFloat16 x
-- Float32
getUnaryArgInfo (LowTypeFloat FloatSize32) (_, TermFloat32 x) =
  return $ UnaryArgInfoFloat32 x
-- Float64
getUnaryArgInfo (LowTypeFloat FloatSize64) (_, TermFloat64 x) =
  return $ UnaryArgInfoFloat64 x
-- otherwise (invalid argument)
getUnaryArgInfo _ _ = Nothing

data BinaryArgInfo
  = BinaryArgInfoIntS IntSize Integer Integer
  | BinaryArgInfoIntU IntSize Integer Integer
  | BinaryArgInfoFloat16 Half Half
  | BinaryArgInfoFloat32 Float Float
  | BinaryArgInfoFloat64 Double Double
  deriving (Show, Eq)

getBinaryArgInfo :: LowType -> TermPlus -> TermPlus -> Maybe BinaryArgInfo
-- IntS
getBinaryArgInfo (LowTypeSignedInt s) (_, TermIntS s1 x) (_, TermIntS s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntS s x y
-- IntU
getBinaryArgInfo (LowTypeUnsignedInt s) (_, TermIntU s1 x) (_, TermIntU s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntU s x y
-- Float16
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, TermFloat16 x) (_, TermFloat16 y) =
  return $ BinaryArgInfoFloat16 x y
-- Float32
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, TermFloat32 x) (_, TermFloat32 y) =
  return $ BinaryArgInfoFloat32 x y
-- Float64
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, TermFloat64 x) (_, TermFloat64 y) =
  return $ BinaryArgInfoFloat64 x y
-- otherwise (invalid arguments)
getBinaryArgInfo _ _ _ = Nothing

computeInt ::
     (Integral a, Bits a)
  => (a -> a -> a) -- asIntS or asIntU
  -> a
  -> a
  -> a
  -> BinaryOp
  -> Either Term a
computeInt k m x y BinaryOpAdd = Right $ k m $ x + y
computeInt k m x y BinaryOpSub = Right $ k m $ x - y
computeInt k m x y BinaryOpMul = Right $ k m $ x * y
computeInt k m x y BinaryOpDiv = Right $ k m $ x `div` y
computeInt k m x y BinaryOpRem = Right $ k m $ x `rem` y
computeInt _ _ x y BinaryOpEQ = Left $ asEpsilon $ x == y
computeInt _ _ x y BinaryOpNE = Left $ asEpsilon $ x /= y
computeInt _ _ x y BinaryOpGT = Left $ asEpsilon $ x > y
computeInt _ _ x y BinaryOpGE = Left $ asEpsilon $ x >= y
computeInt _ _ x y BinaryOpLT = Left $ asEpsilon $ x < y
computeInt _ _ x y BinaryOpLE = Left $ asEpsilon $ x <= y
computeInt k m x y BinaryOpShl = Right $ k m $ shiftL x (unsafeCoerce y)
computeInt k m x y BinaryOpLshr = Right $ k m $ ushiftR' x (unsafeCoerce y)
computeInt k m x y BinaryOpAshr = Right $ k m $ shiftR x (unsafeCoerce y)
computeInt _ _ x y BinaryOpAnd = Right $ x .&. y
computeInt _ _ x y BinaryOpOr = Right $ x .|. y
computeInt _ _ x y BinaryOpXor = Right $ x `xor` y

computeFloat ::
     (Real a, Fractional a) => a -> a -> BinaryOp -> Term -> Either Term a
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

asEpsilon :: Bool -> Term
asEpsilon True = TermEpsilonIntro "true"
asEpsilon False = TermEpsilonIntro "false"
