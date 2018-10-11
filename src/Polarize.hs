module Polarize
  ( polarizeNeg
  ) where

import           Control.Monad

import           Control.Comonad.Cofree

import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import           Util

import           Data.Maybe                 (maybeToList)

polarizeNeg :: Neut -> WithEnv Neg
polarizeNeg (_ :< NeutVar s) = return $ NegUpIntro $ PosVar s
polarizeNeg (_ :< NeutConst s _) = return $ NegUpIntro $ PosConst s
polarizeNeg pi@(_ :< NeutPi _ _) = NegUpIntro <$> polarizePos pi
polarizeNeg lam@(_ :< NeutPiIntro _ _) = NegUpIntro <$> polarizePos lam
polarizeNeg (_ :< NeutPiElim e1 e2) = do
  f <- newNameWith "pi"
  v <- newNameWith "arg"
  bindSeq [(v, e2), (f, e1)] (NegPiElim (NegDownElim (PosVar f)) (PosVar v))
polarizeNeg exists@(_ :< NeutSigma _ _) = NegUpIntro <$> polarizePos exists
polarizeNeg (_ :< NeutSigmaIntro es) = do
  nameList <- mapM (const newName) es
  let nameList' = map PosVar nameList
  bindSeq (zip nameList es) (NegUpIntro (PosSigmaIntro nameList'))
polarizeNeg (_ :< NeutSigmaElim e1 xs e2) = do
  e2' <- polarizeNeg e2
  z <- newNameWith "sigma"
  bindSeq [(z, e1)] (NegSigmaElim (PosVar z) xs e2')
polarizeNeg box@(_ :< NeutBox _) = NegUpIntro <$> polarizePos box
polarizeNeg (_ :< NeutBoxIntro e) = do
  e' <- polarizeNeg e
  return $ NegUpIntro $ PosDownIntro $ NegBoxIntro e'
polarizeNeg (_ :< NeutBoxElim e) = do
  z <- newNameWith "box"
  bindSeq [(z, e)] (NegBoxElim $ NegDownElim (PosVar z))
polarizeNeg t@(_ :< NeutIndex _) = NegUpIntro <$> polarizePos t
polarizeNeg e@(_ :< NeutIndexIntro _) = NegUpIntro <$> polarizePos e
polarizeNeg (_ :< NeutIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarizeNeg es
  x <- newName
  bindSeq [(x, e)] $ NegIndexElim (PosVar x) (zip labelList cs)
polarizeNeg (_ :< NeutMu _ _) = error "polarizeNeg.polarizeNeg: unreachable: Mu"
polarizeNeg t@(_ :< NeutUniv _) = NegUpIntro <$> polarizePos t
polarizeNeg (_ :< NeutHole x) =
  error $ "PolarizeNeg.polarizeNeg: remaining hole: " ++ x

polarizePos :: Neut -> WithEnv Pos
polarizePos (_ :< NeutVar s) = return $ PosVar s
polarizePos (_ :< NeutConst s _) = return $ PosConst s
polarizePos (_ :< NeutPi (x, tdom) tcod) = do
  tdom' <- polarizePos tdom
  tcod' <- PosUp <$> polarizePos tcod
  return $ PosDown $ PosPi (x, tdom') tcod'
polarizePos (_ :< NeutPiIntro (x, _) e) = do
  e' <- polarizeNeg e
  return $ PosDownIntro (NegPiIntro x e')
polarizePos (_ :< NeutPiElim _ _) =
  lift $ throwE "Polarize.polarizePos.NeutPiElim"
polarizePos (_ :< NeutSigma xts body) = do
  body' <- polarizePos body
  let (xs, ts) = unzip xts
  ts' <- mapM polarizePos ts
  let xts' = zip xs ts'
  return $ PosSigma xts' body'
polarizePos (_ :< NeutSigmaIntro es) = do
  es' <- mapM polarizePos es
  return $ PosSigmaIntro es'
polarizePos (_ :< NeutSigmaElim {}) =
  lift $ throwE "Polarize.polarizePos.NeutSigmaElim"
polarizePos (_ :< NeutBox e) = do
  e' <- polarizePos e
  return $ PosDown $ PosBox $ PosUp e'
polarizePos (_ :< NeutBoxIntro e) = do
  e' <- polarizeNeg e
  return $ PosDownIntro $ NegBoxIntro e'
polarizePos (_ :< NeutBoxElim _) =
  lift $ throwE "Polarize.polarizePos.NeutBoxElim"
polarizePos (_ :< NeutIndex l) = return $ PosIndex l
polarizePos (_ :< NeutIndexIntro x) = return $ PosIndexIntro x
polarizePos (_ :< NeutIndexElim _ _) =
  lift $ throwE "Polarize.polarizePos.NeutIndexElim"
polarizePos (_ :< NeutMu _ _) = lift $ throwE "Polarize.polarizePos.NeutMu"
polarizePos (_ :< NeutUniv _) = return PosUniv
polarizePos (_ :< NeutHole _) = lift $ throwE "Polarize.polarizePos.NeutHole"

bindSeq :: [(Identifier, Neut)] -> Neg -> WithEnv Neg
bindSeq [] fun = return fun
bindSeq ((formalArg, arg@(argMeta :< _)):rest) fun = do
  arg' <- polarizeNeg arg
  fun' <- bindSeq rest fun
  argType <- lookupTypeEnv' argMeta
  insTypeEnv formalArg argType
  return $ NegUpElim formalArg arg' fun'
