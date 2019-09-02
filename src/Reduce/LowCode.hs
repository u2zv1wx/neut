module Reduce.LowCode
  ( reduceLowCodePlus
  ) where

import           Control.Monad.State
import           Data.List           (transpose)

import           Data.Basic
import           Data.Env
import           Data.LowCode

reduceLowCodePlus :: LowCodePlus -> WithEnv LowCodePlus
reduceLowCodePlus (m, LowCodeTheta theta) =
  case theta of
    LowDataThetaArith ArithAdd t (m1, LowDataEpsilonIntro (LiteralInteger i1) _) (_, LowDataEpsilonIntro (LiteralInteger i2) _) ->
      return
        ( m
        , LowCodeUpIntro (m1, LowDataEpsilonIntro (LiteralInteger $ i1 + i2) t))
    LowDataThetaArith ArithSub t (m1, LowDataEpsilonIntro (LiteralInteger i1) _) (_, LowDataEpsilonIntro (LiteralInteger i2) _) ->
      return
        ( m
        , LowCodeUpIntro (m1, LowDataEpsilonIntro (LiteralInteger $ i1 - i2) t))
    LowDataThetaArith ArithMul t (m1, LowDataEpsilonIntro (LiteralInteger i1) _) (_, LowDataEpsilonIntro (LiteralInteger i2) _) ->
      return
        ( m
        , LowCodeUpIntro (m1, LowDataEpsilonIntro (LiteralInteger $ i1 * i2) t))
    LowDataThetaArith ArithDiv t (m1, LowDataEpsilonIntro (LiteralInteger i1) _) (_, LowDataEpsilonIntro (LiteralInteger i2) _) ->
      return
        ( m
        , LowCodeUpIntro
            (m1, LowDataEpsilonIntro (LiteralInteger $ i1 `div` i2) t))
    LowDataThetaPrint (_, LowDataEpsilonIntro (LiteralInteger i) _) -> do
      liftIO $ putStr $ show i
      return (m, LowCodeUpIntro (Nothing, LowDataSigmaIntro []))
    _ -> return (m, LowCodeTheta theta)
reduceLowCodePlus (m, LowCodeEpsilonElim (x, t) v branchList) =
  case v of
    (_, LowDataEpsilonIntro l _) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceLowCodePlus $ substLowCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceLowCodePlus $ substLowCodePlus [(x, v)] body
            Nothing   -> return (m, LowCodeEpsilonElim (x, t) v branchList)
    _ -> return (m, LowCodeEpsilonElim (x, t) v branchList)
reduceLowCodePlus (m, LowCodePiElimDownElim v@(_, LowDataTheta x) vs) = do
  cenv <- gets lowCodeEnv
  case lookup x cenv of
    Nothing         -> return (m, LowCodePiElimDownElim v vs)
    Just (xs, body) -> reduceLowCodePlus $ substLowCodePlus (zip xs vs) body
reduceLowCodePlus (m, LowCodeSigmaElim xs v e) =
  case v of
    (_, LowDataSigmaIntro es)
      | length es == length xs ->
        reduceLowCodePlus $ substLowCodePlus (zip xs es) e
    _ -> return (m, LowCodeSigmaElim xs v e)
reduceLowCodePlus (m, LowCodeUpElim x e1 e2) = do
  e1' <- reduceLowCodePlus e1
  case e1' of
    (_, LowCodeUpIntro v) -> reduceLowCodePlus $ substLowCodePlus [(x, v)] e2
    _                     -> return (m, LowCodeUpElim x e1' e2)
reduceLowCodePlus (m, LowCodeCopyN v1 v2) =
  case v1 of
    (_, LowDataEpsilonIntro (LiteralInteger i) _) ->
      return (m, LowCodeUpIntro (m, LowDataSigmaIntro (replicate i v2)))
    _ -> return (m, LowCodeCopyN v1 v2)
reduceLowCodePlus (m, LowCodeTransposeN v vs) =
  case v of
    (_, LowDataEpsilonIntro (LiteralInteger n) _) -> do
      xss <- mapM (const $ newNameList n) vs
      return $
        toSigmaElimSeq
          (zip xss vs)
          ( Nothing
          , LowCodeUpIntro
              ( Nothing
              , LowDataSigmaIntro
                  (map (toSigmaIntro . map toLowDataUpsilon') $ transpose xss)))
    _ -> return (m, LowCodeTransposeN v vs)
reduceLowCodePlus t = return t

newNameList :: Int -> WithEnv [Identifier]
newNameList i = mapM (const $ newNameWith "var") [1 .. i]

toSigmaIntro :: [LowDataPlus] -> LowDataPlus
toSigmaIntro ds = (Nothing, LowDataSigmaIntro ds)

toSigmaElimSeq :: [([Identifier], LowDataPlus)] -> LowCodePlus -> LowCodePlus
toSigmaElimSeq [] cont = cont
toSigmaElimSeq ((xs, d):xsds) cont =
  (Nothing, LowCodeSigmaElim xs d (toSigmaElimSeq xsds cont))
