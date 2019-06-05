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
    -- r1 <- reduceComp e'
    -- liftIO $ putStrLn name
    -- liftIO $ putStrLn $ Pr.ppShow e
    -- let fvs = nub $ varComp e'
    -- liftIO $ putStrLn $ "globalfvs == " ++ show fvs
    hole <- newNameWith "hole"
    insModalEnv name [hole] e'
  menv <- gets modalEnv
  forM_ menv $ \(name, (args, e)) -> do
    liftIO $ putStrLn name
    liftIO $ putStrLn $ Pr.ppShow args
    liftIO $ putStrLn $ Pr.ppShow e
    r0 <- reduceComp e
    liftIO $ putStrLn $ Pr.ppShow r0
    liftIO $ putStrLn "======================="

modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosConst x) = return $ ValueConst x
modalPos (PosSigmaIntro es) = do
  es' <- mapM modalPos es
  return $ ValueSigmaIntro es'
modalPos (PosIndexIntro l t) = return $ ValueIndexIntro l t
modalPos (PosDownIntroPiIntro x e) = do
  e' <- modalNeg e
  modalPosDownIntroPiIntro [x] e'

-- translates (thunk (lam (x1 ... xn) e)).
modalPosDownIntroPiIntro :: [Identifier] -> Comp -> WithEnv Value
modalPosDownIntroPiIntro args body = do
  clsName <- newNameWith "cls"
  insModalEnv clsName args body
  return $ ValueConst clsName

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
-- varValue :: Value -> [Identifier]
-- varValue (ValueVar x) = [x]
-- varValue (ValueConst _) = []
-- varValue (ValueSigmaIntro vs) = concatMap varValue vs
-- varValue (ValueIndexIntro _ _) = []
-- varComp :: Comp -> [Identifier]
-- varComp (CompPiElimDownElim v1 v2) = varValue v1 ++ varValue v2
-- varComp (CompConstElim _ vs) = concatMap varValue vs
-- varComp (CompSigmaElim v xs e) = varValue v ++ filter (`notElem` xs) (varComp e)
-- varComp (CompIndexElim v branchList) = do
--   let (_, es) = unzip branchList
--   varValue v ++ concatMap varComp es
-- varComp (CompUpIntro v) = varValue v
-- varComp (CompUpElim x e1 e2) = varComp e1 ++ filter (/= x) (varComp e2)
