-- interpret downs using boxes.
-- note that ↓N ~ Sigma (A : Ui). Box (A -> N) * A.
module Necessity
  ( necessity
  , necessityPos
  , necessityNeg
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

necessity :: WithEnv ()
necessity = do
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    e' <- necessityPos e
    insSPolEnv name e'

necessityPos :: Pos -> WithEnv SPos
necessityPos (PosVar x) = return $ SPosVar x
necessityPos (PosConst x) = return $ SPosConst x
necessityPos (PosSigmaIntro es) = do
  es' <- mapM necessityPos es
  return $ SPosSigmaIntro es'
necessityPos (PosIndexIntro l meta) = return $ SPosIndexIntro l meta
necessityPos (PosDownIntro e) = do
  let fvs = nub $ varNeg e
  envName <- newNameWith "env"
  e' <- necessityNeg e
  let lam = SNegPiIntro envName $ SNegSigmaElim (SPosVar envName) fvs e'
  return $ SPosSigmaIntro [SPosBoxIntro lam, SPosSigmaIntro $ map SPosVar fvs]

-- necessityPos (PosBoxIntro e) = do
--   e' <- necessityNeg e
--   return $ SPosBoxIntro e'
necessityNeg :: Neg -> WithEnv SNeg
necessityNeg (NegPiIntro x e) = do
  e' <- necessityNeg e
  return $ SNegPiIntro x e'
necessityNeg (NegPiElim e1 e2) = do
  e1' <- necessityNeg e1
  e2' <- necessityPos e2
  return $ SNegPiElim e1' e2'
necessityNeg (NegSigmaElim e1 xs e2) = do
  e1' <- necessityPos e1
  e2' <- necessityNeg e2
  return $ SNegSigmaElim e1' xs e2'
necessityNeg (NegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM necessityNeg es
  e' <- necessityPos e
  return $ SNegIndexElim e' (zip labelList es')
necessityNeg (NegUpIntro v) = do
  v' <- necessityPos v
  return $ SNegUpIntro v'
necessityNeg (NegUpElim x e1 e2) = do
  e1' <- necessityNeg e1
  e2' <- necessityNeg e2
  return $ SNegUpElim x e1' e2'
necessityNeg (NegDownElim e) = do
  e' <- necessityPos e
  envName <- newNameWith "down.elim.env"
  clsName <- newNameWith "down.elim.cls"
  return $
    SNegSigmaElim
      e'
      [clsName, envName]
      (SNegPiElim (SNegBoxElim (SPosVar clsName)) (SPosVar envName))
-- necessityNeg (NegBoxElim e) = do
--   e' <- necessityPos e
--   return $ SNegBoxElim e'
necessityNeg (NegConstElim x es) = do
  es' <- mapM necessityPos es
  return $ SNegConstElim x es'
