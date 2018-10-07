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
polarizeNeg forall@(_ :< NeutPi _ _) = NegUpIntro <$> polarizePos forall
polarizeNeg lam@(_ :< NeutPiIntro _ _) = NegUpIntro <$> polarizePos lam
polarizeNeg e@(_ :< NeutPiElim _ _) = do
  let (fun, identArgList) = toPiElimSeq e
  formalArgs <- mapM (const newName) identArgList
  let (_, argList) = unzip identArgList
  case fun of
    _ :< NeutConst funName _ ->
      bindSeq (zip formalArgs argList) (NegPiElimDownElim funName formalArgs)
    _ -> do
      funName <- newNameWith "fun"
      bindSeq
        (zip formalArgs argList ++ [(funName, fun)])
        (NegPiElimDownElim funName formalArgs)
polarizeNeg exists@(_ :< NeutSigma _ _) = NegUpIntro <$> polarizePos exists
polarizeNeg (_ :< NeutSigmaIntro es) = do
  nameList <- mapM (const newName) es
  let nameList' = map PosVar nameList
  bindSeq (zip nameList es) (NegUpIntro (PosSigmaIntro nameList'))
polarizeNeg (_ :< NeutSigmaElim e1 xs e2) = do
  e2' <- polarizeNeg e2
  z <- newName
  bindSeq [(z, e1)] (NegSigmaElim z xs e2')
polarizeNeg box@(_ :< NeutBox _) = NegUpIntro <$> polarizePos box
polarizeNeg e@(_ :< NeutBoxIntro _) = NegUpIntro <$> polarizePos e
polarizeNeg (_ :< NeutBoxElim e) = do
  x <- newName
  bindSeq [(x, e)] (NegPiElimDownElim x [])
polarizeNeg t@(_ :< NeutIndex _) = NegUpIntro <$> polarizePos t
polarizeNeg e@(_ :< NeutIndexIntro _) = NegUpIntro <$> polarizePos e
polarizeNeg (_ :< NeutIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM polarizeNeg es
  x <- newName
  bindSeq [(x, e)] $ NegIndexElim x (zip labelList cs)
polarizeNeg (_ :< NeutMu s e) = do
  e' <- polarizeNeg e
  insTermEnv s $ Comp e'
  return e'
polarizeNeg t@(_ :< NeutUniv _) = NegUpIntro <$> polarizePos t
polarizeNeg (_ :< NeutHole x) =
  error $ "PolarizeNeg.polarizeNeg: remaining hole: " ++ x

polarizePos :: Neut -> WithEnv Pos
polarizePos (_ :< NeutVar s) = return $ PosVar s
polarizePos (_ :< NeutConst s _) = return $ PosConst s
polarizePos forall@(_ :< NeutPi _ _) = do
  let (body, xts) = toPiSeq forall
  body' <- polarizePos body
  let (xs, ts) = unzip xts
  ts' <- mapM polarizePos ts
  let xts' = zip xs ts'
  return $ PosDown (PosPi xts' (PosUp body'))
polarizePos lam@(i :< NeutPiIntro _ _) = do
  let (body, argTypeMetaList) = toPiIntroSeq lam
  let args = map (\(x, _, _) -> x) argTypeMetaList
  c <- polarizeNeg body
  name <- newNameWith "lam"
  lamType <- lookupTypeEnv' i
  insTypeEnv name lamType
  return $ PosDownIntroPiIntro name args c
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
  return $ PosDown (PosPi [] (PosUp e'))
polarizePos (_ :< NeutBoxIntro e) = do
  e' <- polarizeNeg e
  label <- newNameWith "box"
  return $ PosDownIntroPiIntro label [] e'
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
