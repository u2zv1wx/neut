module Polarize
  ( polarize
  ) where

import Control.Monad

import Control.Comonad.Cofree

import Control.Monad.State
import Control.Monad.Trans.Except

import qualified Text.Show.Pretty as Pr

import Data
import Reduce
import Util

import Data.Maybe (maybeToList)

polarize :: WithEnv ()
polarize = do
  wtenv <- gets weakTermEnv
  forM_ wtenv $ \(name, e) -> do
    e' <- polarizeNeg e
    insPolEnv name e'

polarizeNeg :: Neut -> WithEnv Neg
polarizeNeg (_ :< NeutVar x) = return $ NegUpIntro (PosVar x)
polarizeNeg (_ :< NeutConst x _) = return $ NegUpIntro (PosConst x)
polarizeNeg (_ :< NeutPi (x, tdom) tcod) = do
  dom <- newNameWith "dom"
  cod <- newNameWith "cod"
  bindSeq
    [(dom, tdom), (cod, tcod)]
    (NegUpIntro (PosDown (NegPi (x, PosVar dom) (NegUpIntro (PosVar cod)))))
polarizeNeg (_ :< NeutPiIntro (x, _) e) = do
  e' <- polarizeNeg e
  return $ NegUpIntro (PosDownIntro (NegPiIntro x e'))
polarizeNeg (_ :< NeutPiElim e1 e2) = do
  f <- newNameWith "pi"
  v <- newNameWith "arg"
  bindSeq [(v, e2), (f, e1)] (NegPiElim (NegDownElim (PosVar f)) (PosVar v))
polarizeNeg (_ :< NeutSigma xts body) = do
  let (xs, ts) = unzip xts
  ys <- mapM (const (newNameWith "sigma")) xts
  z <- newNameWith "sigma"
  bindSeq
    (zip (ys ++ [z]) (ts ++ [body]))
    (NegUpIntro (PosSigma (zip xs (map PosVar ys)) (PosVar z)))
polarizeNeg (_ :< NeutSigmaIntro es) = do
  nameList <- mapM (const newName) es
  bindSeq (zip nameList es) (NegUpIntro (PosSigmaIntro (map PosVar nameList)))
polarizeNeg (_ :< NeutSigmaElim e1 xs e2) = do
  e2' <- polarizeNeg e2
  z <- newNameWith "sigma"
  bindSeq [(z, e1)] (NegSigmaElim (PosVar z) xs e2')
polarizeNeg (_ :< NeutBox e) = do
  e' <- polarizeNeg e
  return $ NegUpIntro (PosBox e')
polarizeNeg (_ :< NeutBoxIntro e) = do
  e' <- polarizeNeg e
  return $ NegUpIntro (PosBoxIntro e')
polarizeNeg (_ :< NeutBoxElim e) = do
  z <- newNameWith "box"
  bindSeq [(z, e)] (NegBoxElim $ PosVar z)
polarizeNeg (_ :< NeutIndex l) = return $ NegUpIntro (PosIndex l)
polarizeNeg (_ :< NeutIndexIntro l) = return $ NegUpIntro (PosIndexIntro l)
polarizeNeg (_ :< NeutIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarizeNeg es
  x <- newNameWith "tmp"
  bindSeq [(x, e)] (NegIndexElim (PosVar x) (zip labelList cs))
polarizeNeg (_ :< NeutMu _ _) = error "polarizeNeg.polarizeNeg: unreachable: Mu"
polarizeNeg (_ :< NeutUniv _) = return $ NegUpIntro PosUniv
polarizeNeg (_ :< NeutHole x) =
  error $ "PolarizeNeg.polarizeNeg: remaining hole: " ++ x

bindSeq :: [(Identifier, Neut)] -> Neg -> WithEnv Neg
bindSeq [] fun = return fun
bindSeq ((formalArg, arg):rest) fun = do
  arg' <- polarizeNeg arg
  fun' <- bindSeq rest fun
  return $ NegUpElim formalArg arg' fun'
