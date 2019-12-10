module Reduce.Code
  ( reduceCodePlus
  , inlineCodePlus
  ) where

import Control.Monad.State
import Data.List (transpose)

import Data.Basic
import Data.Code
import Data.Env

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
reduceCodePlus (m, CodeEpsilonElim x v branchList) =
  case v of
    (_, DataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceCodePlus $ substCodePlus [(x, v)] body
            Nothing -> return (m, CodeEpsilonElim x v branchList)
    _ -> return (m, CodeEpsilonElim x v branchList)
reduceCodePlus (m, CodePiElimDownElim v es) = do
  es' <- mapM reduceCodePlus es
  case extractUpIntro es' of
    Nothing -> return (m, CodePiElimDownElim v es')
    Just vs -> do
      cenv <- gets codeEnv
      case (v, exponentArgs es') of
        ((_, DataTheta x), _)
          | Just (xs, body) <- lookup x cenv ->
            reduceCodePlus $ substCodePlus (zip xs vs) body
        _ -> return (m, CodePiElimDownElim v es')
reduceCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> reduceCodePlus $ substCodePlus (zip xs es) e
    _ -> return (m, CodeSigmaElim xs v e)
reduceCodePlus (m, CodeUpIntroSigmaIntroN v1 v2) =
  case v1 of
    (_, DataEpsilonIntro (LiteralInteger i) _) ->
      return (m, CodeUpIntro (m, DataSigmaIntro (replicate i v2)))
    _ -> return (m, CodeUpIntroSigmaIntroN v1 v2)
reduceCodePlus (m, CodeSigmaElimUpIntroSigmaIntroN v vs) =
  case v of
    (_, DataEpsilonIntro (LiteralInteger n) _) -> do
      xss <- mapM (const $ newNameList n) vs
      return $
        toSigmaElimSeq
          (zip xss vs)
          ( Nothing
          , CodeUpIntro
              ( Nothing
              , DataSigmaIntro
                  (map (toSigmaIntro . map toDataUpsilon') $ transpose xss)))
    _ -> return (m, CodeSigmaElimUpIntroSigmaIntroN v vs)
reduceCodePlus t = return t

newNameList :: Int -> WithEnv [Identifier]
newNameList i = mapM (const $ newNameWith "var") [1 .. i]

extractUpIntro :: [CodePlus] -> Maybe [DataPlus]
extractUpIntro [] = Just []
extractUpIntro ((_, CodeUpIntro v):es) = do
  vs <- extractUpIntro es
  return $ v : vs
extractUpIntro _ = Nothing

exponentArgs :: [CodePlus] -> Maybe (Int, DataPlus)
exponentArgs [(_, CodeUpIntro (_, DataEpsilonIntro (LiteralInteger i) _)), (_, CodeUpIntro v)] =
  Just (i, v)
exponentArgs _ = Nothing

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
inlineCodePlus (m, CodeEpsilonElim x v branchList) =
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
              return (m, CodeEpsilonElim x v (zip cs es'))
    _ -> return (m, CodeEpsilonElim x v branchList)
inlineCodePlus (m, CodePiElimDownElim v es) = do
  es' <- mapM inlineCodePlus es
  case extractUpIntro es' of
    Nothing -> return (m, CodePiElimDownElim v es')
    Just vs ->
      case (v, exponentArgs es')
        -- ((_, DataDownIntroPiIntro xs body), _) ->
        --   inlineCodePlus $ substCodePlus (zip xs vs) body
        -- FIXME: reduce theta when the theta is exponent
        -- i.e. reduce `A` recursively in `exponent-i A e`
            of
        _ -> return (m, CodePiElimDownElim v es')
inlineCodePlus (m, CodeSigmaElim xs v e) =
  case v of
    (_, DataSigmaIntro es)
      | length es == length xs -> inlineCodePlus $ substCodePlus (zip xs es) e
    _ -> do
      e' <- inlineCodePlus e
      return (m, CodeSigmaElim xs v e')
inlineCodePlus (m, CodeUpIntroSigmaIntroN v1 v2) =
  case v1 of
    (_, DataEpsilonIntro (LiteralInteger i) _) ->
      return (m, CodeUpIntro (m, DataSigmaIntro (replicate i v2)))
    _ -> return (m, CodeUpIntroSigmaIntroN v1 v2)
inlineCodePlus (m, CodeSigmaElimUpIntroSigmaIntroN v vs) =
  case v of
    (_, DataEpsilonIntro (LiteralInteger n) _) -> do
      xss <- mapM (const $ newNameList n) vs
      return $
        toSigmaElimSeq
          (zip xss vs)
          ( Nothing
          , CodeUpIntro
              ( Nothing
              , DataSigmaIntro
                  (map (toSigmaIntro . map toDataUpsilon') $ transpose xss)))
    _ -> return (m, CodeSigmaElimUpIntroSigmaIntroN v vs)
inlineCodePlus t = return t
