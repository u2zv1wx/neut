module Polarize
  ( polarize
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
  return $ Comp $ Neg $ j :< (NegReturn $ Pos $ i :< PosVar s)
polarize (i :< NeutForall (x, tdom) tcod) = do
  Pos tdom' <- polarize tdom >>= toPos
  Pos tcod' <- polarize tcod >>= toPos
  return $
    Value $ Pos $ i :< PosDown (i :< PosForall (x, tdom') (i :< PosUp tcod'))
polarize lam@(i :< NeutLam _ _) = do
  (body, args) <- toLamSeq lam
  c <- polarize body >>= toNeg
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  insPolTypeEnv i t
  (thunk, t') <- newNameOfTypeDown t
  (ret, _) <- newNameOfTypeUp t'
  return $ Comp $ Neg $ ret :< (NegReturn $ Pos $ thunk :< PosThunkLam args c)
polarize e@(i :< NeutApp _ _) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (j, _) <- newNameOfTypeUp t
  (fun, identArgList) <- funAndArgsPol e
  formalArgs <- mapM (const newName) identArgList
  let (_, argList) = unzip identArgList
  funName <- newNameWith "fun"
  bindSeq
    j
    (zip formalArgs argList ++ [(funName, fun)])
    (Neg $ j :< NegAppForce funName formalArgs)
polarize (i :< NeutExists (x, tdom) tcod) = do
  Pos tdom' <- polarize tdom >>= toPos
  Pos tcod' <- polarize tcod >>= toPos
  return $ Value $ Pos $ i :< PosExists (x, tdom') tcod'
polarize (i :< NeutPair v1 v2) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (j, _) <- newNameOfTypeUp t
  x <- newName
  y <- newName
  bindSeq j [(x, v1), (y, v2)] (Neg $ j :< NegReturn (Pos $ i :< PosPair x y))
polarize (i :< NeutCase e1 (x, y) e2) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  (j, _) <- newNameOfTypeUp t
  Neg e2' <- polarize e2 >>= toNeg
  z <- newName
  bindSeq j [(z, e1)] (Neg $ j :< NegCase z (x, y) e2')
polarize (i :< NeutTop) = return $ Value $ Pos $ i :< PosTop
polarize (i :< NeutUnit) = do
  t <- lookupTypeEnv' i >>= polarize >>= toPos
  insPolTypeEnv i t
  return $ Value $ Pos $ i :< PosUnit
polarize (i :< NeutUniv) = return $ Value $ Pos $ i :< PosUniv
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
  return $ Comp $ Neg $ i :< NegBind formalArg arg' fun'

funAndArgsPol :: Neut -> WithEnv (Neut, [(Identifier, Neut)])
funAndArgsPol (i :< NeutApp e v) = do
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

toLamSeq :: Neut -> WithEnv (Neut, [Identifier])
toLamSeq (_ :< NeutLam (x, _) body) = do
  (body', args) <- toLamSeq body
  return (body', x : args)
toLamSeq t = return (t, [])
