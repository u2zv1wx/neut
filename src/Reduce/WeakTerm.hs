module Reduce.WeakTerm
  ( reduceWeakTerm
  ) where

import           Control.Comonad.Cofree

import           Data.Basic
import           Data.WeakTerm

reduceWeakTerm :: WeakTerm -> WeakTerm
reduceWeakTerm (i :< WeakTermEpsilonElim (x, t) e branchList) = do
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermEpsilonIntro l ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceWeakTerm $ substWeakTerm [(x, e')] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceWeakTerm $ substWeakTerm [(x, e')] body
            Nothing   -> i :< WeakTermEpsilonElim (x, t) e' branchList
    _ -> i :< WeakTermEpsilonElim (x, t) e' branchList
reduceWeakTerm (i :< WeakTermPiElim e es) = do
  let es' = map reduceWeakTerm es
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermPiIntro xts body
      | length xts == length es'
      , all isValue es' -> do
        let xs = map fst xts
        reduceWeakTerm $ substWeakTerm (zip xs es') body
    self@(_ :< WeakTermMu (x, _) body) -> do
      let self' = substWeakTerm [(x, self)] body
      reduceWeakTerm (i :< WeakTermPiElim self' es')
    _ :< WeakTermConst constant
      | [_ :< WeakTermEpsilonIntro (LiteralInteger x), _ :< WeakTermEpsilonIntro (LiteralInteger y)] <-
         es' -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) -> i :< WeakTermEpsilonIntro (LiteralInteger (x + y))
          (_, True, _, _) -> i :< WeakTermEpsilonIntro (LiteralInteger (x - y))
          (_, _, True, _) -> i :< WeakTermEpsilonIntro (LiteralInteger (x * y))
          (_, _, _, True) ->
            i :< WeakTermEpsilonIntro (LiteralInteger (x `div` y))
          _ -> i :< WeakTermPiElim e' es'
    _ -> i :< WeakTermPiElim e' es'
reduceWeakTerm (i :< WeakTermSigmaIntro es) = do
  let es' = map reduceWeakTerm es
  i :< WeakTermSigmaIntro es'
reduceWeakTerm (i :< WeakTermSigmaElim xts e1 e2) = do
  let e1' = reduceWeakTerm e1
  case e1' of
    _ :< WeakTermSigmaIntro es
      | length es == length xts -> do
        let xs = map fst xts
        reduceWeakTerm $ substWeakTerm (zip xs es) e2
    _ -> i :< WeakTermSigmaElim xts e1' e2
reduceWeakTerm (i :< WeakTermTauElim e) = do
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermTauIntro e'' -> reduceWeakTerm e''
    _                         -> i :< WeakTermTauElim e'
reduceWeakTerm (i :< WeakTermThetaElim e) = do
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermThetaIntro e'' -> reduceWeakTerm e''
    _                           -> i :< WeakTermThetaElim e'
reduceWeakTerm (_ :< WeakTermIota e _) = reduceWeakTerm e
reduceWeakTerm t = t
