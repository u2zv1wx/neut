module Reduce.Code
  ( reduceCodePlus
  , inlineCodePlus
  ) where

import           Control.Monad.State

import           Data.Basic
import           Data.Code
import           Data.Env

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

inlineCodePlus :: CodePlus -> WithEnv CodePlus
inlineCodePlus (m, CodeTheta theta) =
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
inlineCodePlus (m, CodeEpsilonElim (x, t) v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> inlineCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> inlineCodePlus $ substCodePlus [(x, v)] body
            Nothing -> do
              let (cs, es) = unzip branchList
              es' <- mapM inlineCodePlus es
              return (m, CodeEpsilonElim (x, t) v (zip cs es'))
    _ -> return (m, CodeEpsilonElim (x, t) v branchList)
inlineCodePlus (m, CodePiElimDownElim v@(_, DataTheta x) vs) = do
  penv <- gets polEnv
  case lookup x penv of
    Nothing         -> return (m, CodePiElimDownElim v vs)
    Just (xs, body) -> inlineCodePlus $ substCodePlus (zip xs vs) body
inlineCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> inlineCodePlus $ substCodePlus (zip xs es) e
    _ -> do
      e' <- inlineCodePlus e
      return (m, CodeSigmaElim xs v e')
inlineCodePlus (m, CodeUpElim x e1 e2) = do
  e1' <- inlineCodePlus e1
  case e1' of
    (_, CodeUpIntro v) -> inlineCodePlus $ substCodePlus [(x, v)] e2
    _ -> do
      e2' <- inlineCodePlus e2
      return (m, CodeUpElim x e1' e2')
inlineCodePlus t = return t
