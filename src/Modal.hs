module Modal
  ( modalize
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.State
import Control.Monad.Trans.Except

import Data.List

import Closure
import Data
import Reduce
import Supply
import Util

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Debug.Trace

modalize :: WithEnv ()
modalize = do
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    e' <- closureNeg e >>= supplySNeg
    let (args, body) = toSNegPiIntroSeq e'
    body' <- modalNeg body
    insModalEnv name args body'
    -- liftIO $ putStrLn "BEFORE:"
    -- liftIO $ putStrLn $ Pr.ppShow e
    -- liftIO $ putStrLn "-------"
    -- liftIO $ putStrLn "BEFORE (Reduced):"
    -- r1 <- reduceNeg e
    -- liftIO $ putStrLn $ Pr.ppShow r1
    -- liftIO $ putStrLn "-------"
    -- liftIO $ putStrLn "AFTER CLOSURE CONV:"
    -- liftIO $ putStrLn $ Pr.ppShow e1
    -- liftIO $ putStrLn "-------"
    -- liftIO $ putStrLn "AFTER CLOSURE CONV (Reduced):"
    -- r2 <- reduceSNeg e1
    -- liftIO $ putStrLn $ Pr.ppShow r2
    -- liftIO $ putStrLn "AFTER SUPPLY (Reduced):"
    -- r3 <- reduceSNeg e'
    -- liftIO $ putStrLn $ Pr.ppShow r3
    -- liftIO $ putStrLn "-------"
    -- undefined
    -- e' <- closureNeg e >>= supplySNeg >>= modalNeg
    -- let (args, body) = toSNegPiIntroSeq e'
    -- insModalEnvConst name body'

modalPos :: SPos -> WithEnv Value
modalPos (SPosVar x) = return $ ValueVar x
modalPos (SPosConst x) = return $ ValueConst x
modalPos (SPosSigmaIntro es) = do
  ds <- mapM modalPos es
  return $ ValueSigmaIntro ds
modalPos (SPosIndexIntro l meta) = return $ ValueIndexIntro l meta
modalPos (SPosBoxIntro e) = do
  let (args, body) = toSNegPiIntroSeq e
  body' <- modalNeg body
  clsName <- newNameWith "cls"
  insModalEnv clsName args body'
  -- insModalEnvFunc clsName args body'
  return $ ValueConst clsName

modalNeg :: SNeg -> WithEnv Comp
modalNeg lam@(SNegPiIntro _ _) = modalNeg $ SNegBoxElim $ SPosBoxIntro lam
modalNeg app@(SNegPiElim _ _) = do
  let (fun, args) = toSNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  xs <- mapM (const (newNameWith "arg")) args
  app' <- commPiElim fun' $ map ValueVar xs
  bindLet (zip xs args') app'
modalNeg (SNegSigmaElim e1 xs e2) = do
  e1' <- modalPos e1
  e2' <- modalNeg e2
  return $ CompSigmaElim e1' xs e2'
modalNeg (SNegIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  es' <- mapM modalNeg es
  e' <- modalPos e
  return $ CompIndexElim e' (zip labelList es')
modalNeg (SNegUpIntro v) = do
  v' <- modalPos v
  return $ CompUpIntro v'
modalNeg (SNegUpElim x e1 e2) = do
  e1' <- modalNeg e1
  e2' <- modalNeg e2
  return $ CompUpElim x e1' e2'
modalNeg (SNegBoxElim e) = do
  e' <- modalPos e
  tmp <- newNameWith "tmp"
  bindLet [(tmp, e')] $ CompPiElimDownElim tmp []
modalNeg (SNegConstElim x es) = do
  es' <- mapM modalPos es
  xs <- mapM (const (newNameWith "arg")) es
  bindLet (zip xs es') $ CompConstElim x xs

bindLet :: [(Identifier, Value)] -> Comp -> WithEnv Comp
bindLet [] e = return e
bindLet ((x, v):rest) e = do
  e' <- bindLet rest e
  return $ CompUpElim x (CompUpIntro v) e'

-- Commutative conversion for pi-elimination
commPiElim :: Comp -> [Value] -> WithEnv Comp
commPiElim (CompPiElimDownElim f xs) args =
  return $ CompPiElimDownElim f (xs ++ args)
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

toSNegPiIntroSeq :: SNeg -> ([Identifier], SNeg)
toSNegPiIntroSeq (SNegPiIntro x body) = do
  let (args, body') = toSNegPiIntroSeq body
  (x : args, body')
toSNegPiIntroSeq t = ([], t)

toSNegPiElimSeq :: SNeg -> (SNeg, [SPos])
toSNegPiElimSeq (SNegPiElim e1 e2) = do
  let (fun, xs) = toSNegPiElimSeq e1
  (fun, e2 : xs)
toSNegPiElimSeq c = (c, [])
