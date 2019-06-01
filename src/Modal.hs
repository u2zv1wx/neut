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
import Necessity
import Reduce
import Supply
import Util

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Debug.Trace

modalize :: WithEnv ()
modalize = do
  spenv <- gets strictPolEnv
  forM_ spenv $ \(name, e) -> do
    actualTerm' <- supplySPos e >>= modalPos
    insModalEnv name actualTerm'
    -- case actualTerm' of
    --   SSPosBoxIntroPiIntro args body -> do
    --     liftIO $ putStrLn $ "name == " ++ show name
    --     liftIO $ putStrLn $ "args == " ++ show args
    --     body' <- modalNeg body
    --     insModalEnv name args body'
    --   _ -> lift $ throwE "non-function?"

modalPos :: SSPos -> WithEnv Value
modalPos (SSPosVar x) = return $ ValueVar x
modalPos (SSPosConst x) = return $ ValueConst x
modalPos (SSPosSigmaIntro es) = do
  ds <- mapM modalPos es
  return $ ValueSigmaIntro ds
modalPos (SSPosIndexIntro l meta) = return $ ValueIndexIntro l meta
modalPos (SSPosBoxIntroPiIntro args body) = do
  body' <- modalNeg body
  -- clsName <- newNameWith "cls"
  return $ ValueBoxIntroPiIntro args body'
  -- insModalEnv clsName args body'
  -- liftIO $ putStrLn $ "name == " ++ show clsName
  -- liftIO $ putStrLn $ "args == " ++ show args
  -- return $ ValueConst clsName

modalNeg :: SSNeg -> WithEnv Comp
modalNeg (SSNegPiElimBoxElim fun args) = do
  fun' <- modalPos fun
  args' <- mapM modalPos args
  tmp <- newNameWith "tmp"
  bindLet [(tmp, fun')] $ CompPiElimBoxElim tmp args'
modalNeg (SSNegSigmaElim e1 xs e2) = do
  e1' <- modalPos e1
  e2' <- modalNeg e2
  return $ CompSigmaElim e1' xs e2'
modalNeg (SSNegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM modalNeg es
  e' <- modalPos e
  return $ CompIndexElim e' (zip labelList es')
modalNeg (SSNegUpIntro v) = do
  v' <- modalPos v
  return $ CompUpIntro v'
modalNeg (SSNegUpElim x e1 e2) = do
  e1' <- modalNeg e1
  e2' <- modalNeg e2
  return $ CompUpElim x e1' e2'
modalNeg (SSNegConstElim x es) = do
  es' <- mapM modalPos es
  xs <- mapM (const (newNameWith "arg")) es
  bindLet (zip xs es') $ CompConstElim x xs

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v):rest) e = do
  e' <- bindLet rest e
  return $ CompUpElim x (CompUpIntro v) e'
