module Polarize
  ( polarize
  , toNeg
  ) where

import           Control.Monad

import           Control.Comonad.Cofree

import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import           Data.Maybe                 (maybeToList)

polarize :: Neut -> WithEnv Term
polarize (_ :< NeutVar s) = return $ Comp $ NegUpIntro $ PosVar s
polarize forall@(_ :< NeutPi _ _) = do
  (body, xts) <- toPiSeq forall
  body' <- polarize body >>= toPos
  let (xs, ts) = unzip xts
  ts' <- mapM (polarize >=> toPos) ts
  let xts' = zip xs ts'
  return $ Value $ PosDown (PosPi xts' (PosUp body'))
polarize lam@(i :< NeutPiIntro _ _) = do
  (body, argTypeMetaList) <- toPiIntroSeq lam
  let args = map (\(x, _, _) -> x) argTypeMetaList
  c <- polarize body >>= toNeg
  name <- newNameWith "lam"
  lamType <- lookupTypeEnv' i
  insTypeEnv name lamType
  return $ Comp $ NegUpIntro $ PosDownIntroPiIntro name args c
polarize e@(_ :< NeutPiElim _ _) = do
  (fun, identArgList) <- funAndArgsPol e
  formalArgs <- mapM (const newName) identArgList
  let (_, argList) = unzip identArgList
  case fun of
    _ :< NeutVar funName ->
      bindSeq (zip formalArgs argList) (NegPiElimDownElim funName formalArgs)
    _ -> do
      funName <- newNameWith "fun"
      bindSeq
        (zip formalArgs argList ++ [(funName, fun)])
        (NegPiElimDownElim funName formalArgs)
polarize exists@(_ :< NeutSigma _ _) = do
  (body, xts) <- toSigmaSeq exists
  body' <- polarize body >>= toPos
  let (xs, ts) = unzip xts
  ts' <- mapM (polarize >=> toPos) ts
  let xts' = zip xs ts'
  return $ Value $ PosSigma xts' body'
polarize pair@(_ :< NeutSigmaIntro _ _) = do
  seq <- toSigmaIntroSeq pair
  nameList <- mapM (const newName) seq
  bindSeq (zip nameList seq) (NegUpIntro (PosSigmaIntro nameList))
polarize (_ :< NeutSigmaElim e1 (x, y) e2) = do
  e2' <- polarize e2 >>= toNeg
  z <- newName
  bindSeq [(z, e1)] (NegSigmaElim z (x, y) e2')
polarize (_ :< NeutBox e) = do
  e' <- polarize e >>= toPos
  return $ Value $ PosDown (PosPi [] (PosUp e'))
polarize (_ :< NeutBoxIntro e) = do
  e' <- polarize e >>= toNeg
  label <- newNameWith "box"
  return $ Comp $ NegUpIntro $ PosDownIntroPiIntro label [] e'
polarize (_ :< NeutBoxElim e) = do
  x <- newName
  bindSeq [(x, e)] (NegPiElimDownElim x [])
polarize (_ :< NeutIndex l) = return $ Value $ PosIndex l
polarize (_ :< NeutIndexIntro x) = return $ Comp $ NegUpIntro $ PosIndexIntro x
polarize (_ :< NeutIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  cs <- mapM (polarize >=> toNeg) es
  x <- newName
  bindSeq [(x, e)] $ NegIndexElim x (zip labelList cs)
polarize (_ :< NeutMu s e) = do
  e' <- polarize e
  undefined
  -- insTermEnv s e'
  return e'
polarize (_ :< NeutUniv _) = return $ Value PosUniv
polarize (_ :< NeutHole x) = error $ "Polarize.polarize: remaining hole: " ++ x

toPos :: Term -> WithEnv Pos
toPos (Value c) = return c
toPos e         = lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"

toNeg :: Term -> WithEnv Neg
toNeg (Comp c) = return c
toNeg e        = lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"

bindSeq :: [(Identifier, Neut)] -> Neg -> WithEnv Term
bindSeq [] fun = return $ Comp fun
bindSeq ((formalArg, arg@(argMeta :< _)):rest) fun = do
  arg' <- polarize arg >>= toNeg
  fun' <- bindSeq rest fun >>= toNeg
  argType <- lookupTypeEnv' argMeta
  insTypeEnv formalArg argType
  return $ Comp $ NegUpElim formalArg arg' fun'

funAndArgsPol :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
funAndArgsPol (i :< NeutPiElim e v) = do
  (fun, xs) <- funAndArgsPol e
  return (fun, (i, v) : xs)
funAndArgsPol c = return (c, [])
