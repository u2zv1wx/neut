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
  undefined
  -- penv <- gets polEnv
  -- forM_ penv $ \(name, e) -> do
  --   e' <- modalNeg e
  --   r0 <- reduceNeg e
  --   -- r1 <- reduceComp e'
  --   liftIO $ putStrLn name
  --   -- liftIO $ putStrLn arg
  --   -- liftIO $ putStrLn $ Pr.ppShow e
  --   liftIO $ putStrLn $ Pr.ppShow r0
  --   -- let fvs = nub $ varComp e'
  --   -- liftIO $ putStrLn $ "globalfvs == " ++ show fvs
  --   -- hole <- newNameWith "hole"
  --   -- insModalEnv name [hole] e'
  --   insModalEnv name e'
  -- menv <- gets modalEnv
  -- forM_ menv $ \(name, (args, e)) -> do
  --   liftIO $ putStrLn name
  --   liftIO $ putStrLn $ Pr.ppShow args
  --   liftIO $ putStrLn $ Pr.ppShow e
  --   r0 <- reduceComp e
  --   liftIO $ putStrLn $ Pr.ppShow r0
  --   liftIO $ putStrLn "======================="

modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosConst x) = return $ ValueConst x
modalPos (PosSigmaIntro es) = do
  es' <- mapM modalPos es
  return $ ValueSigmaIntro es'
modalPos (PosIndexIntro l t) = return $ ValueIndexIntro l t

-- modalPos (PosDownIntroPiIntro x e) = do
--   e' <- modalNeg e
--   -- modalPosDownIntroPiIntro [x] e'
--   clsName <- newNameWith "cls"
--   insModalEnv clsName x e' -- return (thunk (lam (x) e))
--   return $ ValueConst clsName
modalNeg :: Neg -> WithEnv Comp
modalNeg (NegPiElimDownElim v1 v2) = do
  v1' <- modalPos v1
  v2' <- modalPos v2
  return $ CompPiElimDownElim v1' v2'
modalNeg (NegSigmaElim v xs e) = do
  v' <- modalPos v
  e' <- modalNeg e
  return $ CompSigmaElim v' xs e'
modalNeg (NegIndexElim v branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM modalNeg es
  v' <- modalPos v
  return $ CompIndexElim v' (zip labelList es')
modalNeg (NegUpIntro v) = do
  v' <- modalPos v
  return $ CompUpIntro v'
modalNeg (NegUpElim x e1 e2) = do
  e1' <- modalNeg e1
  e2' <- modalNeg e2
  return $ CompUpElim x e1' e2'
modalNeg (NegConstElim x vs) = do
  vs' <- mapM modalPos vs
  return $ CompConstElim x vs'
