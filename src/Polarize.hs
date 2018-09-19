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

polarize :: Neut -> WithEnv Term
polarize (i :< NeutVar s) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  insPolTypeEnv i t
  (j, _) <- newNameOfTypeUp t
  return $ Comp $ Neg $ j :< (NegUpIntro $ Pos $ i :< PosVar s)
polarize forall@(i :< NeutPi _ _) = do
  (body, xts) <- toPiSeq forall
  Pos body' <- polarize body >>= toPos
  let (xs, ts) = unzip xts
  ts' <- mapM (polarize >=> toPos') ts
  let xts' = zip xs ts'
  return $ Value $ Pos $ i :< PosDown (i :< PosPi xts' (i :< PosUp body'))
polarize lam@(i :< NeutPiIntro _ _) = do
  (body, args) <- toPiIntroSeq lam
  c <- polarize body >>= toNeg
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (thunk, t') <- newNameOfTypeDown t
  (ret, _) <- newNameOfTypeUp t'
  return $
    Comp $ Neg $ ret :< (NegUpIntro $ Pos $ thunk :< PosDownIntroPiIntro args c)
polarize e@(i :< NeutPiElim _ _) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (j, _) <- newNameOfTypeUp t
  (fun, identArgList) <- funAndArgsPol e
  formalArgs <- mapM (const newName) identArgList
  let (_, argList) = unzip identArgList
  funName <- newNameWith "fun"
  bindSeq
    j
    (zip formalArgs argList ++ [(funName, fun)])
    (Neg $ j :< NegPiElimDownElim funName formalArgs)
polarize exists@(i :< NeutSigma _ _) = do
  (body, xts) <- toSigmaSeq exists
  Pos body' <- polarize body >>= toPos
  let (xs, ts) = unzip xts
  ts' <- mapM (polarize >=> toPos') ts
  let xts' = zip xs ts'
  return $ Value $ Pos $ i :< PosSigma xts' body'
polarize pair@(i :< NeutSigmaIntro _ _) = do
  seq <- toSigmaIntroSeq pair
  nameList <- mapM (const newName) seq
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (j, _) <- newNameOfTypeUp t
  bindSeq
    j
    (zip nameList seq)
    (Neg $ j :< NegUpIntro (Pos $ i :< PosSigmaIntro nameList))
polarize (i :< NeutSigmaElim e1 (x, y) e2) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (j, _) <- newNameOfTypeUp t
  Neg e2' <- polarize e2 >>= toNeg
  z <- newName
  bindSeq j [(z, e1)] (Neg $ j :< NegSigmaElim z (x, y) e2')
polarize (i :< NeutTop) = return $ Value $ Pos $ i :< PosTop
polarize (i :< NeutTopIntro) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  insPolTypeEnv i t
  return $ Value $ Pos $ i :< PosTopIntro
polarize (i :< NeutUniv j) = return $ Value $ Pos $ i :< PosUniv j
polarize (_ :< NeutHole x) = error $ "Polarize.polarize: remaining hole: " ++ x
polarize (i :< NeutMu s e) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (_, t') <- newNameOfTypeUp t
  insPolTypeEnv i t'
  e' <- polarize e
  insTermEnv s e'
  return e'

toPos :: Term -> WithEnv Pos
toPos (Value (Pos c)) = return $ Pos c
toPos e = lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"

toPos' :: Term -> WithEnv PrePos
toPos' (Value (Pos c)) = return c
toPos' e = lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"

toNeg :: Term -> WithEnv Neg
toNeg (Comp (Neg c)) = return $ Neg c
toNeg e = lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"

bindSeq :: Identifier -> [(Identifier, Neut)] -> Neg -> WithEnv Term
bindSeq _ [] fun = return $ Comp fun
bindSeq i ((formalArg, arg@(meta :< _)):rest) fun = do
  t <- lookupTypeEnv' meta >>= polarize >>= toPos
  insPolTypeEnv formalArg t
  Neg arg' <- polarize arg >>= toNeg
  Neg fun' <- bindSeq i rest fun >>= toNeg
  return $ Comp $ Neg $ i :< NegUpElim formalArg arg' fun'

funAndArgsPol :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
funAndArgsPol (i :< NeutPiElim e v) = do
  (fun, xs) <- funAndArgsPol e
  return (fun, (i, v) : xs)
funAndArgsPol c = return (c, [])

newNameOfTypeUp :: Pos -> WithEnv (Identifier, Pos)
newNameOfTypeUp (Pos t) = do
  meta <- newName
  x <- newNameOfType (Pos $ meta :< PosUp t)
  return (x, Pos $ meta :< PosUp t)

newNameOfTypeDown :: Pos -> WithEnv (Identifier, Pos)
newNameOfTypeDown (Pos t) = do
  meta <- newName
  x <- newNameOfType (Pos $ meta :< PosDown t)
  return (x, Pos $ meta :< PosDown t)

newNameOfType :: Pos -> WithEnv Identifier
newNameOfType t = do
  i <- newName
  insPolTypeEnv i t
  return i

toPiIntroSeq :: Neut -> WithEnv (Neut, [Identifier])
toPiIntroSeq (_ :< NeutPiIntro (x, _) body) = do
  (body', args) <- toPiIntroSeq body
  return (body', x : args)
toPiIntroSeq t = return (t, [])

toSigmaIntroSeq :: Neut -> WithEnv [Neut]
toSigmaIntroSeq (_ :< NeutSigmaIntro e1 e2) = do
  rest <- toSigmaIntroSeq e2
  return $ e1 : rest
toSigmaIntroSeq t = return [t]

toPiSeq :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
toPiSeq (_ :< NeutPi (x, t) body) = do
  (body', args) <- toPiSeq body
  return (body', (x, t) : args)
toPiSeq t = return (t, [])

toSigmaSeq :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
toSigmaSeq (_ :< NeutSigma (x, t) body) = do
  (body', args) <- toSigmaSeq body
  return (body', (x, t) : args)
toSigmaSeq t = return (t, [])
