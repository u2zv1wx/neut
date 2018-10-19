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
    e' <- polarize' e
    insPolEnv name e'
  insArith
  insCopyInt

polarize' :: Neut -> WithEnv Neg
polarize' (_ :< NeutVar x) = return $ NegUpIntro (PosVar x)
polarize' (_ :< NeutConst x _) = return $ NegUpIntro (PosConst x)
polarize' (_ :< NeutPi (x, tdom) tcod) = do
  dom <- newNameWith "dom"
  cod <- newNameWith "cod"
  bindSeq
    [(dom, tdom), (cod, tcod)]
    (NegUpIntro (PosDown (NegPi (x, PosVar dom) (NegUpIntro (PosVar cod)))))
polarize' (_ :< NeutPiIntro (x, _) e) = do
  e' <- polarize' e
  return $ NegUpIntro (PosDownIntro (NegPiIntro x e'))
polarize' (_ :< NeutPiElim e1 e2) = do
  f <- newNameWith "pi"
  v <- newNameWith "arg"
  bindSeq [(v, e2), (f, e1)] (NegPiElim (NegDownElim (PosVar f)) (PosVar v))
polarize' (_ :< NeutSigma xts body) = do
  let (xs, ts) = unzip xts
  ys <- mapM (const (newNameWith "sigma")) xts
  z <- newNameWith "sigma"
  bindSeq
    (zip (ys ++ [z]) (ts ++ [body]))
    (NegUpIntro (PosSigma (zip xs (map PosVar ys)) (PosVar z)))
polarize' (_ :< NeutSigmaIntro es) = do
  nameList <- mapM (const newName) es
  bindSeq (zip nameList es) (NegUpIntro (PosSigmaIntro (map PosVar nameList)))
polarize' (_ :< NeutSigmaElim e1 xs e2) = do
  e2' <- polarize' e2
  z <- newNameWith "sigma"
  bindSeq [(z, e1)] (NegSigmaElim (PosVar z) xs e2')
polarize' (_ :< NeutBox e) = do
  e' <- polarize' e
  return $ NegUpIntro (PosBox e')
polarize' (_ :< NeutBoxIntro e) = do
  e' <- polarize' e
  return $ NegUpIntro (PosBoxIntro e')
polarize' (_ :< NeutBoxElim e) = do
  z <- newNameWith "box"
  bindSeq [(z, e)] (NegBoxElim $ PosVar z)
polarize' (_ :< NeutIndex l) = return $ NegUpIntro (PosIndex l)
polarize' (_ :< NeutIndexIntro l) = return $ NegUpIntro (PosIndexIntro l)
polarize' (_ :< NeutIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarize' es
  x <- newNameWith "tmp"
  bindSeq [(x, e)] (NegIndexElim (PosVar x) (zip labelList cs))
polarize' (_ :< NeutMu x e) = do
  e' <- polarize' e
  return $ NegMu x e'
polarize' (_ :< NeutUniv _) = return $ NegUpIntro PosUniv
polarize' (_ :< NeutHole x) =
  error $ "PolarizeNeg.polarize': remaining hole: " ++ x

bindSeq :: [(Identifier, Neut)] -> Neg -> WithEnv Neg
bindSeq [] fun = return fun
bindSeq ((formalArg, arg):rest) fun = do
  arg' <- polarize' arg
  fun' <- bindSeq rest fun
  return $ NegUpElim formalArg arg' fun'

insArith :: WithEnv ()
insArith =
  forM_ intLowTypeList $ \intLowType -> do
    x <- newNameWith "arg"
    y <- newNameWith "arg"
    meta <- newNameWith "meta"
    insTypeEnv x $ meta :< NeutIndex (show intLowType)
    insTypeEnv y $ meta :< NeutIndex (show intLowType)
    let base e = rt $ NegPiIntro x $ rt $ NegPiIntro y $ NegUpIntro e
    let add = base $ PosArith (ArithAdd, intLowType) (PosVar x) (PosVar y)
    let sub = base $ PosArith (ArithSub, intLowType) (PosVar x) (PosVar y)
    let mul = base $ PosArith (ArithMul, intLowType) (PosVar x) (PosVar y)
    insPolEnv ("core." ++ show intLowType ++ ".add") add
    insPolEnv ("core." ++ show intLowType ++ ".sub") sub
    insPolEnv ("core." ++ show intLowType ++ ".mul") mul

insCopyInt :: WithEnv ()
insCopyInt =
  forM_ intLowTypeList $ \intLowType -> do
    x <- newNameWith "arg"
    let pair = PosSigmaIntro [PosVar x, PosVar x]
    let copy = rt $ NegPiIntro x $ NegUpIntro pair
    insPolEnv ("core." ++ show intLowType ++ ".copy") copy

rt :: Neg -> Neg
rt e = NegUpIntro $ PosDownIntro e
