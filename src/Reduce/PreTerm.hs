module Reduce.PreTerm
  ( reducePreTermPlus
  ) where

import Data.Bits
import Data.Fixed (mod')
import Numeric.Half
import Unsafe.Coerce -- for int -> word, word -> int

import Data.Basic
import Data.Env
import Data.PreTerm

reducePreTermPlus :: PreTermPlus -> WithEnv PreTermPlus
reducePreTermPlus (m, PreTermPi xts cod) = do
  let (xs, ts) = unzip xts
  ts' <- mapM reducePreTermPlus ts
  cod' <- reducePreTermPlus cod
  return $ (m, PreTermPi (zip xs ts') cod')
reducePreTermPlus (m, PreTermPiIntro xts e) = do
  let (xs, ts) = unzip xts
  ts' <- mapM reducePreTermPlus ts
  e' <- reducePreTermPlus e
  return $ (m, PreTermPiIntro (zip xs ts') e')
reducePreTermPlus (m, PreTermPiElim e es) = do
  e' <- reducePreTermPlus e
  es' <- mapM reducePreTermPlus es
  let app = PreTermPiElim e' es'
  case e' of
    (_, PreTermPiIntro xts body)
      | length xts == length es' -- fixme: arguments must be pure (also add partial evaluation)
       -> do
        let xs = map fst xts
        let body' = substPreTermPlus (zip xs es') body
        reducePreTermPlus body'
    self@(_, PreTermMu (x, _) body)
      | all isValue es' -> do
        let self' = substPreTermPlus [(x, self)] body
        reducePreTermPlus (m, PreTermPiElim self' es')
    (_, PreTermConst constant) -> reducePreTermPlusTheta (m, app) es' m constant
    -- (_, PreTermTheta constant) -> reducePreTermPlusTheta (m, app) es' m constant
    _ -> return (m, app)
reducePreTermPlus (m, PreTermMu (x, t) e) = do
  t' <- reducePreTermPlus t
  e' <- reducePreTermPlus e
  return $ (m, PreTermMu (x, t') e')
reducePreTermPlus (m, PreTermConstDecl (x, t) e) = do
  t' <- reducePreTermPlus t
  e' <- reducePreTermPlus e
  return (m, PreTermConstDecl (x, t') e')
reducePreTermPlus (m, PreTermEnumElim e les) = do
  e' <- reducePreTermPlus e
  let (ls, es) = unzip les
  es' <- mapM reducePreTermPlus es
  let les' = zip ls es'
  case e' of
    (_, PreTermEnumIntro l) ->
      case lookup (CaseValue l) les' of
        Just body -> reducePreTermPlus body
        Nothing ->
          case lookup CaseDefault les' of
            Just body -> reducePreTermPlus body
            Nothing -> return (m, PreTermEnumElim e' les')
    _ -> return (m, PreTermEnumElim e' les')
reducePreTermPlus (m, PreTermArray k indexType) = do
  indexType' <- reducePreTermPlus indexType
  return (m, PreTermArray k indexType')
reducePreTermPlus (m, PreTermArrayIntro k les) = do
  let (ls, es) = unzip les
  es' <- mapM reducePreTermPlus es
  return (m, PreTermArrayIntro k $ zip ls es')
reducePreTermPlus (m, PreTermArrayElim k e1 e2) = do
  e1' <- reducePreTermPlus e1
  e2' <- reducePreTermPlus e2
  case (e1', e2') of
    ((_, PreTermArrayIntro k' les), (_, PreTermEnumIntro l))
      | k == k'
      , Just e <- lookup l les -> reducePreTermPlus e
    _ -> return (m, PreTermArrayElim k e1' e2')
reducePreTermPlus e = return e

reducePreTermPlusTheta ::
     PreTermPlus
  -> [PreTermPlus]
  -> PreMeta
  -> Identifier
  -> WithEnv PreTermPlus
reducePreTermPlusTheta orig es m constant
  | Just (lowType, op) <- asUnaryOpMaybe constant
  , [arg] <- es = reducePreTermPlusUnary orig arg m lowType op
  | Just (lowType, op) <- asBinaryOpMaybe constant
  , [arg1, arg2] <- es = reducePreTermPlusBinary orig arg1 arg2 m lowType op
  | otherwise = return orig

reducePreTermPlusUnary ::
     PreTermPlus
  -> PreTermPlus
  -> PreMeta
  -> LowType
  -> UnaryOp
  -> WithEnv PreTermPlus
reducePreTermPlusUnary orig arg m lowType op = do
  case getUnaryArgInfo lowType arg of
    Just (UnaryArgInfoIntS s1 x) ->
      case op of
        UnaryOpTrunc (LowTypeIntS s2)
          | s1 > s2 -> return (m, PreTermIntS s2 (x .&. (2 ^ s2 - 1))) -- e.g. trunc 257 to i8 ~> 257 .&. 255 ~> 1
        UnaryOpZext (LowTypeIntS s2)
          | s1 < s2 -> do
            let s1' = toInteger s1
            let s2' = toInteger s2
            --                      -10 in  i8 {bitseq =           1111 0110}
            -- ~> (asIntU 8)    ~>  246 in  u8 {bitseq =           1111 0110}
            -- ~> (zero extend) ~>  246 in u16 {bitseq = 0000 0000 1111 0110}
            -- ~> (asIntS 16)   ~>  246 in i16 {bitseq = 0000 0000 1111 0110}
            -- (the newly-inserted sign bit is always 0)
            return (m, PreTermIntS s2 (asIntS s2' (asIntU s1' x)))
        UnaryOpSext (LowTypeIntS s2)
          | s1 < s2 -> return (m, PreTermIntS s2 x) -- sext over int doesn't alter interpreted value
        UnaryOpTo (LowTypeFloat FloatSize16) ->
          return (m, PreTermFloat16 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize32) ->
          return (m, PreTermFloat32 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize64) ->
          return (m, PreTermFloat64 (fromIntegral x))
        _ -> return orig
    Just (UnaryArgInfoIntU s1 x) ->
      case op of
        UnaryOpTrunc (LowTypeIntU s2)
          | s1 > s2 -> return (m, PreTermIntU s2 (x .&. (2 ^ s2 - 1))) -- e.g. trunc 257 to i8 ~> 257 .&. 255 ~> 1
        UnaryOpZext (LowTypeIntU s2)
          | s1 < s2 -> return (m, PreTermIntU s2 x) -- zext over uint doesn't alter interpreted value
        UnaryOpSext (LowTypeIntU s2)
          | s1 < s2 -> do
            let s1' = toInteger s1
            let s2' = toInteger s2
            -- when the highest bit is 1:
            --                        246 in  u8 {bitseq =           1111 0110}
            -- ~> (asIntS 8)    ~>    -10 in  i8 {bitseq =           1111 0110}
            -- ~> (sign extend) ~>    -10 in i16 {bitseq = 1111 1111 1111 0110}
            -- ~> (asIntU 16)   ~>  65526 in u16 {bitseq = 1111 1111 1111 0110}
            --
            -- when the highest bit is 0:
            --                      118 in  u8 {bitseq =           0111 0110}
            -- ~> (asIntS 8)    ~>  118 in  i8 {bitseq =           0111 0110}
            -- ~> (sign extend) ~>  118 in i16 {bitseq = 0000 0000 1111 0110}
            -- ~> (asIntU 16)   ~>  118 in u16 {bitseq = 0000 0000 1111 0110}
            return (m, PreTermIntU s2 (asIntU s2' (asIntS s1' x)))
        UnaryOpTo (LowTypeFloat FloatSize16) ->
          return (m, PreTermFloat16 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize32) ->
          return (m, PreTermFloat32 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize64) ->
          return (m, PreTermFloat64 (fromIntegral x))
        _ -> return orig
    Just (UnaryArgInfoFloat16 x) ->
      case op of
        UnaryOpNeg -> return (m, PreTermFloat16 (-x))
        UnaryOpFpExt (LowTypeFloat FloatSize32) ->
          return (m, PreTermFloat32 (realToFrac x))
        UnaryOpFpExt (LowTypeFloat FloatSize64) ->
          return (m, PreTermFloat64 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          return (m, PreTermIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          return (m, PreTermIntU s (asIntU s' (round x)))
        _ -> return orig
    Just (UnaryArgInfoFloat32 x) ->
      case op of
        UnaryOpNeg -> return (m, PreTermFloat32 (-x))
        UnaryOpTrunc (LowTypeFloat FloatSize16) ->
          return (m, PreTermFloat16 (realToFrac x))
        UnaryOpFpExt (LowTypeFloat FloatSize64) ->
          return (m, PreTermFloat64 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          return (m, PreTermIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          return (m, PreTermIntU s (asIntU s' (round x)))
        _ -> return orig
    Just (UnaryArgInfoFloat64 x) ->
      case op of
        UnaryOpNeg -> return (m, PreTermFloat64 (-x))
        UnaryOpTrunc (LowTypeFloat FloatSize16) ->
          return (m, PreTermFloat16 (realToFrac x))
        UnaryOpTrunc (LowTypeFloat FloatSize32) ->
          return (m, PreTermFloat32 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          return (m, PreTermIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          return (m, PreTermIntU s (asIntU s' (round x)))
        _ -> return orig
    Nothing -> return orig

reducePreTermPlusBinary ::
     PreTermPlus
  -> PreTermPlus
  -> PreTermPlus
  -> PreMeta
  -> LowType
  -> BinaryOp
  -> WithEnv PreTermPlus
reducePreTermPlusBinary orig arg1 arg2 m lowType op = do
  case getBinaryArgInfo lowType arg1 arg2 of
    Just (BinaryArgInfoIntS size x y) -> do
      let s = toInteger size
      asPreTermPlus m (computeInt asIntS s x y op) (PreTermIntS size)
    Just (BinaryArgInfoIntU size x y) -> do
      let s = toInteger size
      asPreTermPlus m (computeInt asIntU s x y op) (PreTermIntU size)
    Just (BinaryArgInfoFloat16 x y) ->
      asPreTermPlus m (computeFloat x y op (snd orig)) PreTermFloat16
    Just (BinaryArgInfoFloat32 x y) ->
      asPreTermPlus m (computeFloat x y op (snd orig)) PreTermFloat32
    Just (BinaryArgInfoFloat64 x y) ->
      asPreTermPlus m (computeFloat x y op (snd orig)) PreTermFloat64
    Nothing -> return orig

asPreTermPlus :: Monad m => a -> Either b t -> (t -> b) -> m (a, b)
asPreTermPlus m boolOrCalcResult f =
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

getUnaryArgInfo :: LowType -> PreTermPlus -> Maybe UnaryArgInfo
-- IntS
getUnaryArgInfo (LowTypeIntS s) (_, PreTermIntS s1 x)
  | s == s1 = return $ UnaryArgInfoIntS s x
-- IntU
getUnaryArgInfo (LowTypeIntU s) (_, PreTermIntU s1 x)
  | s == s1 = return $ UnaryArgInfoIntU s x
-- Int with size specified by lowType
getUnaryArgInfo (LowTypeIntS s) (_, PreTermInt x) =
  return $ UnaryArgInfoIntS s x
-- Float16
getUnaryArgInfo (LowTypeFloat FloatSize16) (_, PreTermFloat16 x) =
  return $ UnaryArgInfoFloat16 x
-- Float32
getUnaryArgInfo (LowTypeFloat FloatSize32) (_, PreTermFloat32 x) =
  return $ UnaryArgInfoFloat32 x
-- Float64
getUnaryArgInfo (LowTypeFloat FloatSize64) (_, PreTermFloat64 x) =
  return $ UnaryArgInfoFloat64 x
-- Float with size specified by lowType
getUnaryArgInfo (LowTypeFloat FloatSize16) (_, PreTermFloat x) =
  return $ UnaryArgInfoFloat16 (realToFrac x)
getUnaryArgInfo (LowTypeFloat FloatSize32) (_, PreTermFloat x) =
  return $ UnaryArgInfoFloat32 (realToFrac x)
getUnaryArgInfo (LowTypeFloat FloatSize64) (_, PreTermFloat x) =
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

getBinaryArgInfo :: LowType -> PreTermPlus -> PreTermPlus -> Maybe BinaryArgInfo
-- IntS
getBinaryArgInfo (LowTypeIntS s) (_, PreTermIntS s1 x) (_, PreTermIntS s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeIntS s) (_, PreTermInt x) (_, PreTermIntS s2 y)
  | s == s2 = return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeIntS s) (_, PreTermIntS s1 x) (_, PreTermInt y)
  | s == s1 = return $ BinaryArgInfoIntS s x y
-- IntU
getBinaryArgInfo (LowTypeIntU s) (_, PreTermIntU s1 x) (_, PreTermIntU s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntU s x y
getBinaryArgInfo (LowTypeIntU s) (_, PreTermInt x) (_, PreTermIntU s2 y)
  | s == s2 = return $ BinaryArgInfoIntU s x y
getBinaryArgInfo (LowTypeIntU s) (_, PreTermIntU s1 x) (_, PreTermInt y)
  | s == s1 = return $ BinaryArgInfoIntU s x y
-- Int with size specified by lowType
getBinaryArgInfo (LowTypeIntS s) (_, PreTermInt x) (_, PreTermInt y) =
  return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeIntU s) (_, PreTermInt x) (_, PreTermInt y) =
  return $ BinaryArgInfoIntU s x y
-- Float16
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, PreTermFloat16 x) (_, PreTermFloat16 y) =
  return $ BinaryArgInfoFloat16 x y
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, PreTermFloat x) (_, PreTermFloat16 y) =
  return $ BinaryArgInfoFloat16 (realToFrac x) y
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, PreTermFloat16 x) (_, PreTermFloat y) =
  return $ BinaryArgInfoFloat16 x (realToFrac y)
-- Float32
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, PreTermFloat32 x) (_, PreTermFloat32 y) =
  return $ BinaryArgInfoFloat32 x y
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, PreTermFloat x) (_, PreTermFloat32 y) =
  return $ BinaryArgInfoFloat32 (realToFrac x) y
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, PreTermFloat32 x) (_, PreTermFloat y) =
  return $ BinaryArgInfoFloat32 x (realToFrac y)
-- Float64
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, PreTermFloat64 x) (_, PreTermFloat64 y) =
  return $ BinaryArgInfoFloat64 x y
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, PreTermFloat x) (_, PreTermFloat64 y) =
  return $ BinaryArgInfoFloat64 (realToFrac x) y
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, PreTermFloat64 x) (_, PreTermFloat y) =
  return $ BinaryArgInfoFloat64 x (realToFrac y)
-- Float with size specified by lowType
getBinaryArgInfo (LowTypeFloat FloatSize16) (_, PreTermFloat x) (_, PreTermFloat y) =
  return $ BinaryArgInfoFloat16 (realToFrac x) (realToFrac y)
getBinaryArgInfo (LowTypeFloat FloatSize32) (_, PreTermFloat x) (_, PreTermFloat y) =
  return $ BinaryArgInfoFloat32 (realToFrac x) (realToFrac y)
getBinaryArgInfo (LowTypeFloat FloatSize64) (_, PreTermFloat x) (_, PreTermFloat y) =
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
  -> Either PreTerm a
computeInt k m x y BinaryOpAdd = Right $ k m $ x + y
computeInt k m x y BinaryOpSub = Right $ k m $ x - y
computeInt k m x y BinaryOpMul = Right $ k m $ x * y
computeInt k m x y BinaryOpDiv = Right $ k m $ x `div` y
computeInt k m x y BinaryOpRem = Right $ k m $ x `rem` y
computeInt _ _ x y BinaryOpEQ = Left $ asEnum $ x == y
computeInt _ _ x y BinaryOpNE = Left $ asEnum $ x /= y
computeInt _ _ x y BinaryOpGT = Left $ asEnum $ x > y
computeInt _ _ x y BinaryOpGE = Left $ asEnum $ x >= y
computeInt _ _ x y BinaryOpLT = Left $ asEnum $ x < y
computeInt _ _ x y BinaryOpLE = Left $ asEnum $ x <= y
computeInt k m x y BinaryOpShl = Right $ k m $ shiftL x (unsafeCoerce y)
computeInt k m x y BinaryOpLshr = Right $ k m $ ushiftR' x (unsafeCoerce y)
computeInt k m x y BinaryOpAshr = Right $ k m $ shiftR x (unsafeCoerce y)
computeInt _ _ x y BinaryOpAnd = Right $ x .&. y
computeInt _ _ x y BinaryOpOr = Right $ x .|. y
computeInt _ _ x y BinaryOpXor = Right $ x `xor` y

computeFloat ::
     (Real a, Fractional a) => a -> a -> BinaryOp -> PreTerm -> Either PreTerm a
computeFloat x y BinaryOpAdd _ = Right $ x + y
computeFloat x y BinaryOpSub _ = Right $ x - y
computeFloat x y BinaryOpMul _ = Right $ x * y
computeFloat x y BinaryOpDiv _ = Right $ x / y
computeFloat x y BinaryOpRem _ = Right $ x `mod'` y
computeFloat x y BinaryOpEQ _ = Left $ asEnum $ x == y
computeFloat x y BinaryOpNE _ = Left $ asEnum $ x /= y
computeFloat x y BinaryOpGT _ = Left $ asEnum $ x > y
computeFloat x y BinaryOpGE _ = Left $ asEnum $ x >= y
computeFloat x y BinaryOpLT _ = Left $ asEnum $ x < y
computeFloat x y BinaryOpLE _ = Left $ asEnum $ x <= y
computeFloat _ _ _ e = Left e

asEnum :: Bool -> PreTerm
asEnum True = PreTermEnumIntro $ EnumValueLabel "true"
asEnum False = PreTermEnumIntro $ EnumValueLabel "false"
