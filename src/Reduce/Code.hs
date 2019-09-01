module Reduce.Code
  ( reduceCodePlus
  ) where

import           Control.Monad.State

import           Data.Basic
import           Data.Code
import           Data.Env

-- reduceCodePlus :: CodePlus -> WithEnv CodePlus
-- reduceCodePlus (m, CodeTheta theta) =
--   case theta of
--     ThetaArith ArithAdd (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
--       return (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 + i2)))
--     ThetaArith ArithSub (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
--       return (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 - i2)))
--     ThetaArith ArithMul (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
--       return (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 * i2)))
--     ThetaArith ArithDiv (m1, DataEpsilonIntro (LiteralInteger i1)) (_, DataEpsilonIntro (LiteralInteger i2)) ->
--       return
--         (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 `div` i2)))
--     ThetaPrint (_, DataEpsilonIntro (LiteralInteger i)) -> do
--       liftIO $ putStr $ show i
--       let topType = (DataMetaTerminal Nothing, DataEpsilon "top")
--       let topMeta = DataMetaNonTerminal topType Nothing
--       return (m, CodeUpIntro (topMeta, DataEpsilonIntro (LiteralLabel "unit")))
--     _ -> return (m, CodeTheta theta)
-- reduceCodePlus (m, CodeEpsilonElim (x, t) v branchList) =
--   case v of
--     (_, DataEpsilonIntro l) ->
--       case lookup (CaseLiteral l) branchList of
--         Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
--         Nothing ->
--           case lookup CaseDefault branchList of
--             Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
--             Nothing   -> return (m, CodeEpsilonElim (x, t) v branchList)
--     _ -> return (m, CodeEpsilonElim (x, t) v branchList)
-- reduceCodePlus (m, CodePiElimDownElim v@(_, DataTheta x) vs) = do
--   penv <- gets polEnv
--   case lookup x penv of
--     Nothing -> return (m, CodePiElimDownElim v vs)
--     Just (xts, body) -> do
--       let xs = map fst xts
--       reduceCodePlus $ substCodePlus (zip xs vs) body
-- reduceCodePlus (m, CodeSigmaElim xts v e) =
--   case v of
--     (_, DataSigmaIntro es)
--       | length es == length xts -> do
--         let xs = map fst xts
--         reduceCodePlus $ substCodePlus (zip xs es) e
--     _ -> return (m, CodeSigmaElim xts v e)
-- reduceCodePlus (m, CodeUpElim (x, t) e1 e2) = do
--   e1' <- reduceCodePlus e1
--   case e1' of
--     (_, CodeUpIntro v) -> reduceCodePlus $ substCodePlus [(x, v)] e2
--     _                  -> return (m, CodeUpElim (x, t) e1' e2)
-- reduceCodePlus t = return t
-- module Reduce.Code
--   ( reduceCodePlus
--   ) where
-- import           Control.Monad.State
-- import           Data.List           (transpose)
-- import           Data.Basic
-- import           Data.Code
-- import           Data.Env
reduceCodePlus :: CodePlus -> WithEnv CodePlus
reduceCodePlus (m, CodeTheta theta) =
  case theta of
    ThetaArith ArithAdd t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 + i2) t))
    ThetaArith ArithSub t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 - i2) t))
    ThetaArith ArithMul t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 * i2) t))
    ThetaArith ArithDiv t (m1, DataEpsilonIntro (LiteralInteger i1) _) (_, DataEpsilonIntro (LiteralInteger i2) _) ->
      return
        (m, CodeUpIntro (m1, DataEpsilonIntro (LiteralInteger $ i1 `div` i2) t))
    ThetaPrint (_, DataEpsilonIntro (LiteralInteger i) _) -> do
      liftIO $ putStr $ show i
      return (m, CodeUpIntro (Nothing, DataSigmaIntro []))
    _ -> return (m, CodeTheta theta)
reduceCodePlus (m, CodeEpsilonElim (x, t) v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
            Nothing   -> return (m, CodeEpsilonElim (x, t) v branchList)
    _ -> return (m, CodeEpsilonElim (x, t) v branchList)
reduceCodePlus (m, CodePiElimDownElim v@(_, DataTheta x) vs) = do
  penv <- gets polEnv
  case lookup x penv of
    Nothing         -> return (m, CodePiElimDownElim v vs)
    Just (xs, body) -> reduceCodePlus $ substCodePlus (zip xs vs) body
reduceCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> reduceCodePlus $ substCodePlus (zip xs es) e
    _ -> return (m, CodeSigmaElim xs v e)
reduceCodePlus (m, CodeUpElim x e1 e2) = do
  e1' <- reduceCodePlus e1
  case e1' of
    (_, CodeUpIntro v) -> reduceCodePlus $ substCodePlus [(x, v)] e2
    _                  -> return (m, CodeUpElim x e1' e2)
-- reduceCodePlus (m, CodeCopyN v1 v2) =
--   case v1 of
--     (_, DataEpsilonIntro (LiteralInteger i) _) ->
--       return (m, CodeUpIntro (m, DataSigmaIntro (replicate i v2)))
--     _ -> return (m, CodeCopyN v1 v2)
-- reduceCodePlus (m, CodeTransposeN v vs) =
--   case v of
--     (_, DataEpsilonIntro (LiteralInteger n) _) -> do
--       xss <- mapM (const $ newNameList n) vs
--       return $
--         toSigmaElimSeq
--           (zip xss vs)
--           ( Nothing
--           , CodeUpIntro
--               ( Nothing
--               , DataSigmaIntro
--                   (map (toSigmaIntro . map toDataUpsilon') $ transpose xss)))
--     _ -> return (m, CodeTransposeN v vs)
reduceCodePlus t = return t

newNameList :: Int -> WithEnv [Identifier]
newNameList i = mapM (const $ newNameWith "var") [1 .. i]

toSigmaIntro :: [DataPlus] -> DataPlus
toSigmaIntro ds = (Nothing, DataSigmaIntro ds)

toSigmaElimSeq :: [([Identifier], DataPlus)] -> CodePlus -> CodePlus
toSigmaElimSeq [] cont = cont
toSigmaElimSeq ((xs, d):xsds) cont =
  (Nothing, CodeSigmaElim xs d (toSigmaElimSeq xsds cont))
