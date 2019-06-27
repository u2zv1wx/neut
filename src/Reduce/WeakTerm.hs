module Reduce.WeakTerm
  ( reduceWeakTerm
  ) where

import           Control.Comonad.Cofree

import           Data.Basic
import           Data.WeakTerm

reduceWeakTerm :: WeakTerm -> WeakTerm
reduceWeakTerm (i :< WeakTermEpsilonElim (t, x) e branchList) = do
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermEpsilonIntro l ->
      case lookup (CaseLiteral l) branchList of
        Just body -> reduceWeakTerm $ substWeakTerm [(x, e')] body
        Nothing ->
          case lookup CaseDefault branchList of
            Just body -> reduceWeakTerm $ substWeakTerm [(x, e')] body
            Nothing   -> i :< WeakTermEpsilonElim (t, x) e' branchList
    _ -> i :< WeakTermEpsilonElim (t, x) e' branchList
reduceWeakTerm (i :< WeakTermPiElim s e es) = do
  let es' = map reduceWeakTerm es
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermPiIntro _ txs body
      | length txs == length es'
      , all isValue es' -> do
        let xs = map snd txs
        reduceWeakTerm $ substWeakTerm (zip xs es') body
    self@(_ :< WeakTermRec (_, x) body) -> do
      let self' = substWeakTerm [(x, self)] body
      reduceWeakTerm (i :< WeakTermPiElim s self' es')
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
          _ -> i :< WeakTermPiElim s e' es'
    _ -> i :< WeakTermPiElim s e' es'
reduceWeakTerm (i :< WeakTermSigmaIntro s es) = do
  let es' = map reduceWeakTerm es
  i :< WeakTermSigmaIntro s es'
reduceWeakTerm (i :< WeakTermSigmaElim s txs e1 e2) = do
  let e1' = reduceWeakTerm e1
  case e1' of
    _ :< WeakTermSigmaIntro _ es
      | length es == length txs -> do
        let xs = map snd txs
        reduceWeakTerm $ substWeakTerm (zip xs es) e2
    _ -> i :< WeakTermSigmaElim s txs e1' e2
reduceWeakTerm t = t
