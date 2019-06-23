module Reduce.WeakTerm
  ( reduceWeakTerm
  ) where

import           Control.Comonad.Cofree

import           Data.Basic
import           Data.WeakTerm

reduceWeakTerm :: WeakTerm -> WeakTerm
reduceWeakTerm (i :< WeakTermUpsilon u) =
  i :< WeakTermUpsilon (reduceWeakTermUpsilon u)
reduceWeakTerm (i :< WeakTermEpsilonElim e branchList) = do
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermEpsilonIntro l ->
      case lookup (WeakCaseLiteral l) branchList of
        Just body -> reduceWeakTerm body
        Nothing ->
          case lookup WeakCaseDefault branchList of
            Just body -> reduceWeakTerm body
            Nothing   -> i :< WeakTermEpsilonElim e' branchList
    _ -> i :< WeakTermEpsilonElim e' branchList
reduceWeakTerm (i :< WeakTermPi s uts) = do
  let uts' = map reduceWeakTermUpsilon' uts
  i :< WeakTermPi (reduceWeakTermSortal s) uts'
reduceWeakTerm (i :< WeakTermPiIntro s uts e) = do
  let uts' = map reduceWeakTermUpsilon' uts
  i :< WeakTermPiIntro (reduceWeakTermSortal s) uts' e
reduceWeakTerm (i :< WeakTermPiElim s e es) = do
  let s' = reduceWeakTermSortal s
  let es' = map reduceWeakTerm es
  let e' = reduceWeakTerm e
  case e' of
    _ :< WeakTermPiIntro _ uts body
      | length uts == length es -> do
        let xs = map (snd . fst) uts
        reduceWeakTerm $ substWeakTerm (zip xs es') body
    self@(_ :< WeakTermRec ((_, x), _) body) -> do
      let self' = substWeakTerm [(x, self)] body
      reduceWeakTerm (i :< WeakTermPiElim s' self' es')
    _ :< WeakTermConst constant
      | [_ :< WeakTermEpsilonIntro (WeakLiteralInteger x ma), _ :< WeakTermEpsilonIntro (WeakLiteralInteger y _)] <-
         es' -> do
        let b1 = constant `elem` intAddConstantList
        let b2 = constant `elem` intSubConstantList
        let b3 = constant `elem` intMulConstantList
        let b4 = constant `elem` intDivConstantList
        case (b1, b2, b3, b4) of
          (True, _, _, _) ->
            i :< WeakTermEpsilonIntro (WeakLiteralInteger (x + y) ma)
          (_, True, _, _) ->
            i :< WeakTermEpsilonIntro (WeakLiteralInteger (x - y) ma)
          (_, _, True, _) ->
            i :< WeakTermEpsilonIntro (WeakLiteralInteger (x * y) ma)
          (_, _, _, True) ->
            i :< WeakTermEpsilonIntro (WeakLiteralInteger (x `div` y) ma)
          _ -> i :< WeakTermPiElim s' e' es'
    _ -> i :< WeakTermPiElim s' e' es'
reduceWeakTerm (i :< WeakTermSigma s uts) = do
  let uts' = map reduceWeakTermUpsilon' uts
  i :< WeakTermSigma (reduceWeakTermSortal s) uts'
reduceWeakTerm (i :< WeakTermSigmaIntro s es) = do
  let s' = reduceWeakTermSortal s
  let es' = map reduceWeakTerm es
  i :< WeakTermSigmaIntro s' es'
reduceWeakTerm (i :< WeakTermSigmaElim s uts e1 e2) = do
  let s' = reduceWeakTermSortal s
  let e1' = reduceWeakTerm e1
  case e1' of
    _ :< WeakTermSigmaIntro _ es
      | length es == length uts -> do
        let xs = map (snd . fst) uts
        reduceWeakTerm $ substWeakTerm (zip xs es) e2
    _ -> do
      let uts' = map reduceWeakTermUpsilon' uts
      i :< WeakTermSigmaElim s' uts' e1' e2
reduceWeakTerm (i :< WeakTermRec ut e) =
  i :< WeakTermRec (reduceWeakTermUpsilon' ut) e
reduceWeakTerm t = t

reduceWeakTermSortal :: Sortal -> Sortal
reduceWeakTermSortal SortalPrimitive = SortalPrimitive
reduceWeakTermSortal (SortalTerm e)  = SortalTerm $ reduceWeakTerm e

reduceWeakTermUpsilon :: Upsilon -> Upsilon
reduceWeakTermUpsilon (s, x) = (reduceWeakTermSortal s, x)

reduceWeakTermUpsilon' :: (Upsilon, WeakTerm) -> (Upsilon, WeakTerm)
reduceWeakTermUpsilon' (u, t) = (reduceWeakTermUpsilon u, t)
