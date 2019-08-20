module Reduce.WeakCode
  ( reduceWeakCodePlus
  ) where

import           Data.Basic
import           Data.Env
import           Data.WeakCode

reduceWeakCodePlus :: WeakCodePlus -> WithEnv WeakCodePlus
reduceWeakCodePlus (m, WeakCodeEpsilonElim (x, t) v branchList) =
  case v of
    (_, WeakDataEpsilonIntro l) ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceWeakCodePlus $ substWeakCodePlus [(x, v)] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceWeakCodePlus $ substWeakCodePlus [(x, v)] body
            Nothing   -> return (m, WeakCodeEpsilonElim (x, t) v branchList)
    _ -> return (m, WeakCodeEpsilonElim (x, t) v branchList)
reduceWeakCodePlus (m, WeakCodePiElim e vs) = do
  e' <- reduceWeakCodePlus e
  case e' of
    (_, WeakCodePiIntro xts body)
      | length xts == length vs -> do
        let xs = map fst xts
        reduceWeakCodePlus $ substWeakCodePlus (zip xs vs) body
    self@(m', WeakCodeMu (x, t) body) -> do
      let meta = WeakMetaNonTerminal t (obtainLocation m')
      let x' = (meta, WeakDataDownIntro self)
      let self' = substWeakCodePlus [(x, x')] body
      reduceWeakCodePlus (m, WeakCodePiElim self' vs)
    (_, WeakCodeDownElim (_, WeakDataTheta constant))
      | [(m1, WeakDataEpsilonIntro (LiteralInteger x)), (_, WeakDataEpsilonIntro (LiteralInteger y))] <-
         vs -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        let up d = return (m, WeakCodeUpIntro d)
        case (b1, b2, b3, b4) of
          (True, _, _, _) ->
            up (m1, WeakDataEpsilonIntro (LiteralInteger (x + y)))
          (_, True, _, _) ->
            up (m1, WeakDataEpsilonIntro (LiteralInteger (x - y)))
          (_, _, True, _) ->
            up (m1, WeakDataEpsilonIntro (LiteralInteger (x * y)))
          (_, _, _, True) ->
            up (m1, WeakDataEpsilonIntro (LiteralInteger (x `div` y)))
          _ -> return (m, WeakCodePiElim e' vs)
    _ -> return (m, WeakCodePiElim e' vs)
reduceWeakCodePlus (m, WeakCodeSigmaElim xts v e) =
  case v of
    (_, WeakDataSigmaIntro es)
      | length es == length xts -> do
        let xs = map fst xts
        reduceWeakCodePlus $ substWeakCodePlus (zip xs es) e
    _ -> return (m, WeakCodeSigmaElim xts v e)
reduceWeakCodePlus (m, WeakCodeUpElim (x, t) e1 e2) = do
  e1' <- reduceWeakCodePlus e1
  case e1' of
    (_, WeakCodeUpIntro v) -> reduceWeakCodePlus $ substWeakCodePlus [(x, v)] e2
    _ -> return (m, WeakCodeUpElim (x, t) e1' e2)
reduceWeakCodePlus (m, WeakCodeDownElim v) =
  case v of
    (_, WeakDataDownIntro e) -> reduceWeakCodePlus e
    _                        -> return (m, WeakCodeDownElim v)
reduceWeakCodePlus t = return t

obtainLocation :: WeakMeta -> Maybe (Int, Int)
obtainLocation (WeakMetaTerminal ml)      = ml
obtainLocation (WeakMetaNonTerminal _ ml) = ml
