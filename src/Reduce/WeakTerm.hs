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
reduceWeakTermPlus (m, WeakTermPi xts cod) = do
  let (xs, ts) = unzip xts
  ts' <- mapM reduceWeakTermPlus ts
  cod' <- reduceWeakTermPlus cod
  return (m, WeakTermPi (zip xs ts') cod')
reduceWeakTermPlus (m, WeakTermPiIntro xts e) = do
  let (xs, ts) = unzip xts
  ts' <- mapM reduceWeakTermPlus ts
  e' <- reduceWeakTermPlus e
  return $ (m, WeakTermPiIntro (zip xs ts') e')
reduceWeakTermPlus (m, WeakTermPiElim e es) = do
  e' <- reduceWeakTermPlus e
  es' <- mapM reduceWeakTermPlus es
  let app = WeakTermPiElim e' es'
  case e' of
    (_, WeakTermPiIntro xts body)
      | length xts == length es' -> do
        let xs = map fst xts
        reduceWeakTermPlus $ substWeakTermPlus (zip xs es') body
    (_, WeakTermIter (x, _) xts body)
      | x `notElem` varWeakTermPlus body
      , length xts == length es' -> do
        let xs = map fst xts
        reduceWeakTermPlus $ substWeakTermPlus (zip xs es') body
    (_, WeakTermConst constant) ->
      reduceWeakTermPlusTheta (m, app) es' m constant
    _ -> return (m, app)
-- reduceWeakTermPlus (m, WeakTermIter (x, t) xts e)
--   | x `notElem` varWeakTermPlus e = do undefined
reduceWeakTermPlus (m, WeakTermIter (x, t) xts e) = do
  t' <- reduceWeakTermPlus t
  e' <- reduceWeakTermPlus e
  let (xs, ts) = unzip xts
  ts' <- mapM reduceWeakTermPlus ts
  return $ (m, WeakTermIter (x, t') (zip xs ts') e')
reduceWeakTermPlus (m, WeakTermConstDecl (x, t) e) = do
  t' <- reduceWeakTermPlus t
  e' <- reduceWeakTermPlus e
  return (m, WeakTermConstDecl (x, t') e')
reduceWeakTermPlus (m, WeakTermEnumElim e les) = do
  e' <- reduceWeakTermPlus e
  let (ls, es) = unzip les
  es' <- mapM reduceWeakTermPlus es
  let les' = zip ls es'
  case e' of
    (_, WeakTermEnumIntro l) ->
      case lookup (CaseValue l) les' of
        Just body -> reduceWeakTermPlus body
        Nothing ->
          case lookup CaseDefault les' of
            Just body -> reduceWeakTermPlus body
            Nothing -> return (m, WeakTermEnumElim e' les')
    _ -> return (m, WeakTermEnumElim e' les')
reduceWeakTermPlus (m, WeakTermArray k indexType) = do
  indexType' <- reduceWeakTermPlus indexType
  return (m, WeakTermArray k indexType')
reduceWeakTermPlus (m, WeakTermArrayIntro k les) = do
  let (ls, es) = unzip les
  es' <- mapM reduceWeakTermPlus es
  return (m, WeakTermArrayIntro k $ zip ls es')
reduceWeakTermPlus (m, WeakTermArrayElim k e1 e2) = do
  e1' <- reduceWeakTermPlus e1
  e2' <- reduceWeakTermPlus e2
  case (e1', e2') of
    ((_, WeakTermArrayIntro k' les), (_, WeakTermEnumIntro l))
      | k == k'
      , Just e <- lookup l les -> reduceWeakTermPlus e
    _ -> return (m, WeakTermArrayElim k e1' e2')
reduceWeakTermPlus e = return e

reduceWeakTermPlusTheta ::
     WeakTermPlus
  -> [WeakTermPlus]
  -> PreMeta
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
  -> PreMeta
  -> LowType
  -> UnaryOp
  -> WithEnv WeakTermPlus
reduceWeakTermPlusUnary orig arg m lowType op = do
  case getUnaryArgInfo lowType arg of
    Just (UnaryArgInfoIntS s1 x) ->
      case op of
        UnaryOpTrunc (LowTypeIntS s2)
          | s1 > s2 -> return (m, WeakTermIntS s2 (x .&. (2 ^ s2 - 1))) -- e.g. trunc 257 to i8 ~> 257 .&. 255 ~> 1
        UnaryOpZext (LowTypeIntS s2)
          | s1 < s2 -> do
            let s1' = toInteger s1
            let s2' = toInteger s2
            --                      -10 in  i8 {bitseq =           1111 0110}
            -- ~> (asIntU 8)    ~>  246 in  u8 {bitseq =           1111 0110}
            -- ~> (zero extend) ~>  246 in u16 {bitseq = 0000 0000 1111 0110}
            -- ~> (asIntS 16)   ~>  246 in i16 {bitseq = 0000 0000 1111 0110}
            -- (the newly-inserted sign bit is always 0)
            return (m, WeakTermIntS s2 (asIntS s2' (asIntU s1' x)))
        UnaryOpSext (LowTypeIntS s2)
          | s1 < s2 -> return (m, WeakTermIntS s2 x) -- sext over int doesn't alter interpreted value
        UnaryOpTo (LowTypeFloat FloatSize16) ->
          return (m, WeakTermFloat16 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize32) ->
          return (m, WeakTermFloat32 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize64) ->
          return (m, WeakTermFloat64 (fromIntegral x))
        _ -> return orig
    Just (UnaryArgInfoIntU s1 x) ->
      case op of
        UnaryOpTrunc (LowTypeIntU s2)
          | s1 > s2 -> return (m, WeakTermIntU s2 (x .&. (2 ^ s2 - 1))) -- e.g. trunc 257 to i8 ~> 257 .&. 255 ~> 1
        UnaryOpZext (LowTypeIntU s2)
          | s1 < s2 -> return (m, WeakTermIntU s2 x) -- zext over uint doesn't alter interpreted value
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
            return (m, WeakTermIntU s2 (asIntU s2' (asIntS s1' x)))
        UnaryOpTo (LowTypeFloat FloatSize16) ->
          return (m, WeakTermFloat16 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize32) ->
          return (m, WeakTermFloat32 (fromIntegral x))
        UnaryOpTo (LowTypeFloat FloatSize64) ->
          return (m, WeakTermFloat64 (fromIntegral x))
        _ -> return orig
    Just (UnaryArgInfoFloat16 x) ->
      case op of
        UnaryOpNeg -> return (m, WeakTermFloat16 (-x))
        UnaryOpFpExt (LowTypeFloat FloatSize32) ->
          return (m, WeakTermFloat32 (realToFrac x))
        UnaryOpFpExt (LowTypeFloat FloatSize64) ->
          return (m, WeakTermFloat64 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          return (m, WeakTermIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          return (m, WeakTermIntU s (asIntU s' (round x)))
        _ -> return orig
    Just (UnaryArgInfoFloat32 x) ->
      case op of
        UnaryOpNeg -> return (m, WeakTermFloat32 (-x))
        UnaryOpTrunc (LowTypeFloat FloatSize16) ->
          return (m, WeakTermFloat16 (realToFrac x))
        UnaryOpFpExt (LowTypeFloat FloatSize64) ->
          return (m, WeakTermFloat64 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          return (m, WeakTermIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          return (m, WeakTermIntU s (asIntU s' (round x)))
        _ -> return orig
    Just (UnaryArgInfoFloat64 x) ->
      case op of
        UnaryOpNeg -> return (m, WeakTermFloat64 (-x))
        UnaryOpTrunc (LowTypeFloat FloatSize16) ->
          return (m, WeakTermFloat16 (realToFrac x))
        UnaryOpTrunc (LowTypeFloat FloatSize32) ->
          return (m, WeakTermFloat32 (realToFrac x))
        UnaryOpTo (LowTypeIntS s) -> do
          let s' = toInteger s
          return (m, WeakTermIntS s (asIntS s' (round x)))
        UnaryOpTo (LowTypeIntU s) -> do
          let s' = toInteger s
          return (m, WeakTermIntU s (asIntU s' (round x)))
        _ -> return orig
    Nothing -> return orig

reduceWeakTermPlusBinary ::
     WeakTermPlus
  -> WeakTermPlus
  -> WeakTermPlus
  -> PreMeta
  -> LowType
  -> BinaryOp
  -> WithEnv WeakTermPlus
reduceWeakTermPlusBinary orig arg1 arg2 m lowType op = do
  case getBinaryArgInfo lowType arg1 arg2 of
    Just (BinaryArgInfoIntS size x y) -> do
      let s = toInteger size
      asWeakTermPlus m (computeInt asIntS s x y op) (WeakTermIntS size)
    Just (BinaryArgInfoIntU size x y) -> do
      let s = toInteger size
      asWeakTermPlus m (computeInt asIntU s x y op) (WeakTermIntU size)
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
getUnaryArgInfo (LowTypeIntS s) (_, WeakTermIntS s1 x)
  | s == s1 = return $ UnaryArgInfoIntS s x
-- IntU
getUnaryArgInfo (LowTypeIntU s) (_, WeakTermIntU s1 x)
  | s == s1 = return $ UnaryArgInfoIntU s x
-- Int with size specified by lowType
getUnaryArgInfo (LowTypeIntS s) (_, WeakTermInt x) =
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
getBinaryArgInfo (LowTypeIntS s) (_, WeakTermIntS s1 x) (_, WeakTermIntS s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeIntS s) (_, WeakTermInt x) (_, WeakTermIntS s2 y)
  | s == s2 = return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeIntS s) (_, WeakTermIntS s1 x) (_, WeakTermInt y)
  | s == s1 = return $ BinaryArgInfoIntS s x y
-- IntU
getBinaryArgInfo (LowTypeIntU s) (_, WeakTermIntU s1 x) (_, WeakTermIntU s2 y)
  | s == s1 && s == s2 = return $ BinaryArgInfoIntU s x y
getBinaryArgInfo (LowTypeIntU s) (_, WeakTermInt x) (_, WeakTermIntU s2 y)
  | s == s2 = return $ BinaryArgInfoIntU s x y
getBinaryArgInfo (LowTypeIntU s) (_, WeakTermIntU s1 x) (_, WeakTermInt y)
  | s == s1 = return $ BinaryArgInfoIntU s x y
-- Int with size specified by lowType
getBinaryArgInfo (LowTypeIntS s) (_, WeakTermInt x) (_, WeakTermInt y) =
  return $ BinaryArgInfoIntS s x y
getBinaryArgInfo (LowTypeIntU s) (_, WeakTermInt x) (_, WeakTermInt y) =
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

computeInt ::
     (Integral a, Bits a)
  => (a -> a -> a) -- asIntS or asIntU
  -> a
  -> a
  -> a
  -> BinaryOp
  -> Either WeakTerm a
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
computeFloat x y BinaryOpEQ _ = Left $ asEnum $ x == y
computeFloat x y BinaryOpNE _ = Left $ asEnum $ x /= y
computeFloat x y BinaryOpGT _ = Left $ asEnum $ x > y
computeFloat x y BinaryOpGE _ = Left $ asEnum $ x >= y
computeFloat x y BinaryOpLT _ = Left $ asEnum $ x < y
computeFloat x y BinaryOpLE _ = Left $ asEnum $ x <= y
computeFloat _ _ _ e = Left e

asEnum :: Bool -> WeakTerm
asEnum True = WeakTermEnumIntro $ EnumValueLabel "true"
asEnum False = WeakTermEnumIntro $ EnumValueLabel "false"
