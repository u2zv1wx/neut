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
  insPrintInt

polarize' :: Neut -> WithEnv Neg
polarize' (_ :< NeutVar x) = return $ NegUpIntro (PosVar x)
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
polarize' (meta :< NeutIndexIntro l) =
  return $ NegUpIntro (PosIndexIntro l meta)
polarize' (_ :< NeutIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarize' es
  x <- newNameWith "tmp"
  bindSeq [(x, e)] (NegIndexElim (PosVar x) (zip labelList cs))
polarize' (_ :< NeutMu x e) = do
  e' <- polarize' e
  return $ NegMu x e'
polarize' (_ :< NeutConst t) = do
  x <- newNameWith "const"
  bindSeq [(x, t)] $ NegUpIntro $ PosConst $ PosVar x
polarize' (_ :< NeutConstIntro x) = return $ NegUpIntro (PosConstIntro x)
polarize' (_ :< NeutConstElim e) = do
  x <- newNameWith "const"
  bindSeq [(x, e)] $ NegConstElim $ PosVar x
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
insArith = do
  let numLowTypeList = intLowTypeList ++ floatLowTypeList
  forM_ numLowTypeList $ \numLowType -> do
    (x, y) <- prepareVariables numLowType
    let base e = rb $ rt $ NegPiIntro x $ rt $ NegPiIntro y $ NegUpIntro e
    let add = base $ PosArith (ArithAdd, numLowType) (PosVar x) (PosVar y)
    let sub = base $ PosArith (ArithSub, numLowType) (PosVar x) (PosVar y)
    let mul = base $ PosArith (ArithMul, numLowType) (PosVar x) (PosVar y)
    let div = base $ PosArith (ArithDiv, numLowType) (PosVar x) (PosVar y)
    insPolEnv ("core." ++ show numLowType ++ ".add") add
    insPolEnv ("core." ++ show numLowType ++ ".sub") sub
    insPolEnv ("core." ++ show numLowType ++ ".mul") mul
    insPolEnv ("core." ++ show numLowType ++ ".div") div

prepareVariables :: LowType -> WithEnv (Identifier, Identifier)
prepareVariables lowType = do
  x <- newNameWith "arg"
  y <- newNameWith "arg"
  meta <- newNameWith "meta"
  insTypeEnv x $ meta :< NeutIndex (show lowType)
  insTypeEnv y $ meta :< NeutIndex (show lowType)
  return (x, y)

insCopyInt :: WithEnv ()
insCopyInt =
  forM_ intLowTypeList $ \intLowType -> do
    x <- newNameWith "arg"
    let pair = PosSigmaIntro [PosVar x, PosVar x]
    let copy = rb $ rt $ NegPiIntro x $ NegUpIntro pair
    insPolEnv ("core." ++ show intLowType ++ ".copy") copy

insPrintInt :: WithEnv ()
insPrintInt =
  forM_ [LowTypeSignedInt 32] $ \intLowType
  -- forM_ intLowTypeList $ \intLowType -> do
   -> do
    x <- newNameWith "arg"
    let print = rb $ rt $ NegPiIntro x $ NegPrint intLowType (PosVar x)
    insPolEnv ("core." ++ show intLowType ++ ".print") print

rt :: Neg -> Neg
rt e = NegUpIntro $ PosDownIntro e

rb :: Neg -> Neg
rb e = NegUpIntro $ PosBoxIntro e
