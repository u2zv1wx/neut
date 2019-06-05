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
    liftIO $ putStrLn name
    liftIO $ putStrLn $ Pr.ppShow e
    -- let fvs = nub $ varComp e'
    -- liftIO $ putStrLn $ "globalfvs == " ++ show fvs
    insModalEnv name [] e'
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
modalPos (PosDownIntro e) = do
  e' <- modalNeg e
  modalPosDownIntroPiIntro [] e'

-- translates (thunk (lam (x1 ... xn) e)).
modalPosDownIntroPiIntro :: [Identifier] -> Comp -> WithEnv Value
modalPosDownIntroPiIntro args body = do
  clsName <- newNameWith "cls"
  insModalEnv clsName args body
  return $ ValueConst clsName

modalNeg :: Neg -> WithEnv Comp
modalNeg lam@(NegPiIntro _ _) = do
  let (args, body) = toNegPiIntroSeq lam
  body' <- modalNeg body
  let fvs = filter (`notElem` args) $ nub $ varComp body'
  v <- modalPosDownIntroPiIntro (fvs ++ args) body'
  return $ CompPiElimDownElim v $ map ValueVar fvs
modalNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  commPiElim fun' args'
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
modalNeg (NegDownElim v) = do
  v' <- modalPos v
  return $ CompPiElimDownElim v' []
modalNeg (NegConstElim x vs) = do
  vs' <- mapM modalPos vs
  return $ CompConstElim x vs'

commPiElim :: Comp -> [Value] -> WithEnv Comp
commPiElim (CompPiElimDownElim v vs) args =
  return $ CompPiElimDownElim v (vs ++ args)
commPiElim (CompConstElim c vs) args = return $ CompConstElim c (vs ++ args)
commPiElim (CompSigmaElim v xs e) args = do
  e' <- commPiElim e args
  return $ CompSigmaElim v xs e'
commPiElim (CompIndexElim v branchList) args = do
  let (labelList, es) = unzip branchList
  es' <- mapM (`commPiElim` args) es
  return $ CompIndexElim v (zip labelList es')
commPiElim (CompUpIntro v) [] = return $ CompUpIntro v
commPiElim (CompUpIntro _) _ = lift $ throwE "Modal.commPiElim: type error"
commPiElim (CompUpElim x e1 e2) args = do
  e2' <- commPiElim e2 args
  return $ CompUpElim x e1 e2'

toNegPiIntroSeq :: Neg -> ([Identifier], Neg)
toNegPiIntroSeq (NegPiIntro x body) = do
  let (args, body') = toNegPiIntroSeq body
  (x : args, body')
toNegPiIntroSeq t = ([], t)

toNegPiElimSeq :: Neg -> (Neg, [Pos])
toNegPiElimSeq (NegPiElim e v) = do
  let (fun, vs) = toNegPiElimSeq e
  (fun, vs ++ [v])
toNegPiElimSeq c = (c, [])

varValue :: Value -> [Identifier]
varValue (ValueVar x) = [x]
varValue (ValueConst _) = []
varValue (ValueSigmaIntro vs) = concatMap varValue vs
varValue (ValueIndexIntro _ _) = []

varComp :: Comp -> [Identifier]
varComp (CompPiElimDownElim v vs) = varValue v ++ concatMap varValue vs
varComp (CompConstElim _ vs) = concatMap varValue vs
varComp (CompSigmaElim v xs e) = varValue v ++ filter (`notElem` xs) (varComp e)
varComp (CompIndexElim v branchList) = do
  let (_, es) = unzip branchList
  varValue v ++ concatMap varComp es
varComp (CompUpIntro v) = varValue v
varComp (CompUpElim x e1 e2) = varComp e1 ++ filter (/= x) (varComp e2)
