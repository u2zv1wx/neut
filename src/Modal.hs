module Modal
  ( modalize
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except

import Data.List

import Data
import Reduce
import Util

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Debug.Trace

modalize :: WithEnv ()
modalize = do
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    e' <- modalNeg e
    insModalEnv name [] e'

modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosConst x) = return $ ValueConst x
modalPos (PosSigmaIntro es) = do
  es' <- mapM modalPos es
  return $ ValueSigmaIntro es'
modalPos (PosIndexIntro l t) = return $ ValueIndexIntro l t
modalPos (PosDownIntro e) = do
  e' <- modalNeg e
  modalPosBoxIntroPiIntro [] e'

-- translates (thunk (lam (x1 ... xn) e)).
modalPosBoxIntroPiIntro :: [Identifier] -> Comp -> WithEnv Value
modalPosBoxIntroPiIntro args body = do
  clsName <- newNameWith "cls"
  insModalEnv clsName args body
  return $ ValueConst clsName

modalNeg :: Neg -> WithEnv Comp
modalNeg lam@(NegPiIntro _ _) = do
  let (args, body) = toNegPiIntroSeq lam
  let fvs = filter (`notElem` args) $ varNeg body
  body' <- modalNeg body
  v <- modalPosBoxIntroPiIntro (fvs ++ args) body'
  return $ CompPiElimBoxElim v $ map ValueVar fvs
modalNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  commPiElim fun' args'
modalNeg (NegSigmaElim e1 xs e2) = do
  e1' <- modalPos e1
  e2' <- modalNeg e2
  return $ CompSigmaElim e1' xs e2'
modalNeg (NegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM modalNeg es
  e' <- modalPos e
  return $ CompIndexElim e' (zip labelList es')
modalNeg (NegUpIntro v) = do
  v' <- modalPos v
  return $ CompUpIntro v'
modalNeg (NegUpElim x e1 e2) = do
  e1' <- modalNeg e1
  e2' <- modalNeg e2
  return $ CompUpElim x e1' e2'
modalNeg (NegDownElim v) = do
  v' <- modalPos v
  return $ CompPiElimBoxElim v' []
modalNeg (NegConstElim x es) = do
  es' <- mapM modalPos es
  xs <- mapM (const (newNameWith "arg")) es
  bindLet (zip xs es') $ CompConstElim x xs

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v):rest) e = do
  e' <- bindLet rest e
  return $ CompUpElim x (CompUpIntro v) e'

commPiElim :: Comp -> [Value] -> WithEnv Comp
commPiElim (CompPiElimBoxElim f xs) args =
  return $ CompPiElimBoxElim f (xs ++ args)
commPiElim (CompSigmaElim v xs e) args = do
  e' <- commPiElim e args
  return $ CompSigmaElim v xs e'
commPiElim (CompIndexElim v branchList) args = do
  let (labelList, es) = unzip branchList
  es' <- mapM (`commPiElim` args) es
  return $ CompIndexElim v (zip labelList es')
commPiElim (CompUpElim x e1 e2) args = do
  e2' <- commPiElim e2 args
  return $ CompUpElim x e1 e2'
commPiElim _ _ = lift $ throwE "Modal.commPiElim: type error"

toNegPiIntroSeq :: Neg -> ([Identifier], Neg)
toNegPiIntroSeq (NegPiIntro x body) = do
  let (args, body') = toNegPiIntroSeq body
  (x : args, body')
toNegPiIntroSeq t = ([], t)

toNegPiElimSeq :: Neg -> (Neg, [Pos])
toNegPiElimSeq (NegPiElim e1 e2) = do
  let (fun, xs) = toNegPiElimSeq e1
  (fun, e2 : xs)
toNegPiElimSeq c = (c, [])
