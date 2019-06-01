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

supplySPos :: SPos -> WithEnv SSPos
supplySPos (SPosVar x) = return $ SSPosVar x
supplySPos (SPosConst x) = return $ SSPosConst x
supplySPos (SPosSigmaIntro es) = do
  es' <- mapM supplySPos es
  return $ SSPosSigmaIntro es'
supplySPos (SPosIndexIntro l meta) = return $ SSPosIndexIntro l meta
supplySPos (SPosBoxIntro e) = do
  e' <- supplySNeg e
  return $ SSPosBoxIntroPiIntro [] e' -- argが0個なのでただのboxintro.

supplySNeg :: SNeg -> WithEnv SSNeg
supplySNeg lam@(SNegPiIntro _ _) = do
  let (args, body) = toSNegPiIntroSeq lam
  body' <- supplySNeg body
  let fvs = filter (`notElem` args) $ varSNeg body
  return $
    SSNegPiElimBoxElim
      (SSPosBoxIntroPiIntro (fvs ++ args) body')
      (map SSPosVar fvs)
  -- return $ SSNegPiElimBoxElim (SSPosBoxIntroPiIntro (fvs ++ args) body') []
supplySNeg app@(SNegPiElim _ _) = do
  let (fun, args) = toSNegPiElimSeq app
  fun' <- supplySNeg fun
  args' <- mapM supplySPos args
  commPiElim fun' args'
supplySNeg (SNegSigmaElim e1 xs e2) = do
  e1' <- supplySPos e1
  e2' <- supplySNeg e2
  return $ SSNegSigmaElim e1' xs e2'
supplySNeg (SNegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM supplySNeg es
  e' <- supplySPos e
  return $ SSNegIndexElim e' (zip labelList es')
supplySNeg (SNegUpIntro v) = do
  v' <- supplySPos v
  return $ SSNegUpIntro v'
supplySNeg (SNegUpElim x e1 e2) = do
  e1' <- supplySNeg e1
  e2' <- supplySNeg e2
  return $ SSNegUpElim x e1' e2'
supplySNeg (SNegBoxElim e) = do
  e' <- supplySPos e
  return $ SSNegPiElimBoxElim e' [] -- ふつうのbox-elim.
supplySNeg (SNegConstElim x es) = do
  es' <- mapM supplySPos es
  return $ SSNegConstElim x es'

toSNegPiIntroSeq :: SNeg -> ([Identifier], SNeg)
toSNegPiIntroSeq (SNegPiIntro x body) = do
  let (args, body') = toSNegPiIntroSeq body
  (x : args, body')
toSNegPiIntroSeq t = ([], t)

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

varSPos :: SPos -> [Identifier]
varSPos (SPosVar s) = [s]
varSPos (SPosConst _) = []
varSPos (SPosSigmaIntro es) = concatMap varSPos es
varSPos (SPosIndexIntro _ _) = []
varSPos (SPosBoxIntro e) = varSNeg e

varSNeg :: SNeg -> [Identifier]
varSNeg (SNegPiIntro x e) = filter (/= x) $ varSNeg e
varSNeg (SNegPiElim e1 e2) = varSNeg e1 ++ varSPos e2
varSNeg (SNegSigmaElim e1 xs e2) = do
  let vs1 = varSPos e1
  let vs2 = filter (`notElem` xs) $ varSNeg e2
  vs1 ++ vs2
varSNeg (SNegIndexElim e branchList) = do
  let vs1 = varSPos e
  let vs2 = concatMap (varSNeg . snd) branchList
  vs1 ++ vs2
varSNeg (SNegUpIntro e) = varSPos e
varSNeg (SNegUpElim x e1 e2) = do
  let vs1 = varSNeg e1
  let vs2 = filter (/= x) $ varSNeg e2
  vs1 ++ vs2
varSNeg (SNegBoxElim e) = varSPos e
varSNeg (SNegConstElim _ es) = concatMap varSPos es

toSNegPiElimSeq :: SNeg -> (SNeg, [SPos])
toSNegPiElimSeq (SNegPiElim e1 e2) = do
  let (fun, xs) = toSNegPiElimSeq e1
  (fun, e2 : xs)
toSNegPiElimSeq c = (c, [])
