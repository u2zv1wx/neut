-- eliminates all the free variables from every lambda-sequence.
module Supply
  ( supplySPos
  , supplySNeg
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

supplySPos :: Pos -> WithEnv SSPos
supplySPos (PosVar x) = return $ SSPosVar x
supplySPos (PosConst x) = return $ SSPosConst x
supplySPos (PosSigmaIntro es) = do
  es' <- mapM supplySPos es
  return $ SSPosSigmaIntro es'
supplySPos (PosIndexIntro l meta) = return $ SSPosIndexIntro l meta
supplySPos (PosDownIntro e) = do
  e' <- supplySNeg e
  return $ SSPosBoxIntroPiIntro [] e'

supplySNeg :: Neg -> WithEnv SSNeg
supplySNeg lam@(NegPiIntro _ _) = do
  let (args, body) = toNegPiIntroSeq lam
  body' <- supplySNeg body
  let fvs = filter (`notElem` args) $ varSSNeg body'
  return $
    SSNegPiElimBoxElim
      (SSPosBoxIntroPiIntro (fvs ++ args) body')
      (map SSPosVar fvs)
supplySNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- supplySNeg fun
  args' <- mapM supplySPos args
  commPiElim fun' args'
supplySNeg (NegSigmaElim e1 xs e2) = do
  e1' <- supplySPos e1
  e2' <- supplySNeg e2
  return $ SSNegSigmaElim e1' xs e2'
supplySNeg (NegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM supplySNeg es
  e' <- supplySPos e
  return $ SSNegIndexElim e' (zip labelList es')
supplySNeg (NegUpIntro v) = do
  v' <- supplySPos v
  return $ SSNegUpIntro v'
supplySNeg (NegUpElim x e1 e2) = do
  e1' <- supplySNeg e1
  e2' <- supplySNeg e2
  return $ SSNegUpElim x e1' e2'
supplySNeg (NegDownElim e) = do
  e' <- supplySPos e
  return $ SSNegPiElimBoxElim e' []
supplySNeg (NegConstElim x es) = do
  es' <- mapM supplySPos es
  return $ SSNegConstElim x es'

toNegPiIntroSeq :: Neg -> ([Identifier], Neg)
toNegPiIntroSeq (NegPiIntro x body) = do
  let (args, body') = toNegPiIntroSeq body
  (x : args, body')
toNegPiIntroSeq t = ([], t)

commPiElim :: SSNeg -> [SSPos] -> WithEnv SSNeg
commPiElim (SSNegPiElimBoxElim f xs) args =
  return $ SSNegPiElimBoxElim f (xs ++ args)
commPiElim (SSNegSigmaElim v xs e) args = do
  e' <- commPiElim e args
  return $ SSNegSigmaElim v xs e'
commPiElim (SSNegIndexElim v branchList) args = do
  let (labelList, es) = unzip branchList
  es' <- mapM (`commPiElim` args) es
  return $ SSNegIndexElim v (zip labelList es')
commPiElim (SSNegUpElim x e1 e2) args = do
  e2' <- commPiElim e2 args
  return $ SSNegUpElim x e1 e2'
commPiElim _ _ = lift $ throwE "Modal.commPiElim: type error"

varSSPos :: SSPos -> [Identifier]
varSSPos (SSPosVar s) = [s]
varSSPos (SSPosConst _) = []
varSSPos (SSPosSigmaIntro es) = concatMap varSSPos es
varSSPos (SSPosIndexIntro _ _) = []
varSSPos (SSPosBoxIntroPiIntro args e) = filter (`notElem` args) $ varSSNeg e

varSSNeg :: SSNeg -> [Identifier]
varSSNeg (SSNegPiElimBoxElim e args) = varSSPos e ++ concatMap varSSPos args
varSSNeg (SSNegSigmaElim e1 xs e2) = do
  let vs1 = varSSPos e1
  let vs2 = filter (`notElem` xs) $ varSSNeg e2
  vs1 ++ vs2
varSSNeg (SSNegIndexElim e branchList) = do
  let vs1 = varSSPos e
  let vs2 = concatMap (varSSNeg . snd) branchList
  vs1 ++ vs2
varSSNeg (SSNegUpIntro e) = varSSPos e
varSSNeg (SSNegUpElim x e1 e2) = do
  let vs1 = varSSNeg e1
  let vs2 = filter (/= x) $ varSSNeg e2
  vs1 ++ vs2
varSSNeg (SSNegConstElim _ es) = concatMap varSSPos es

toNegPiElimSeq :: Neg -> (Neg, [Pos])
toNegPiElimSeq (NegPiElim e1 e2) = do
  let (fun, xs) = toNegPiElimSeq e1
  (fun, e2 : xs)
toNegPiElimSeq c = (c, [])
