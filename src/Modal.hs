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
  penv <- gets polEnv
  forM_ penv $ \(name, e) -> do
    let name' = name ++ ".fun"
    -- e' <- supplySNeg e
    -- let body = SSNegUpIntro actualTerm'
    e'' <- modalNeg e
    insModalEnv name' [] e''
    -- insModalEnvFunc name' [] e''
    -- insModalEnvConst name actualTerm'
  -- menv <- gets modalEnv
  -- forM_ menv $ \(name, e) -> do
  --   liftIO $ putStrLn $ "the arity of " ++ name ++ " is " ++ show (arity e)
    -- case actualTerm' of
    --   SSPosBoxIntroPiIntro args body -> do
    --     liftIO $ putStrLn $ "name == " ++ show name
    --     liftIO $ putStrLn $ "args == " ++ show args
    --     body' <- modalNeg body
    --     insModalEnv name args body'
    --   _ -> lift $ throwE "non-function?"

-- modalPos :: SSPos -> WithEnv Value
-- modalPos (SSPosVar x) = return $ ValueVar x
-- modalPos (SSPosConst x) = return $ ValueConst x
-- modalPos (SSPosSigmaIntro es) = do
--   ds <- mapM modalPos es
--   return $ ValueSigmaIntro ds
-- modalPos (SSPosIndexIntro l meta) = return $ ValueIndexIntro l meta
-- modalPos (SSPosBoxIntroPiIntro args body) = do
--   body' <- modalNeg body
--   clsName <- newNameWith "cls"
--   -- return $ ValueBoxIntroPiIntro args body'
--   insModalEnv clsName args body'
--   -- insModalEnvFunc clsName args body'
--   -- liftIO $ putStrLn $ "name == " ++ show clsName
--   -- liftIO $ putStrLn $ "args == " ++ show args
--   return $ ValueConst clsName
modalPos :: Pos -> WithEnv Value
modalPos (PosVar x) = return $ ValueVar x
modalPos (PosConst x) = return $ ValueConst x
modalPos (PosSigmaIntro es) = do
  es' <- mapM modalPos es
  return $ ValueSigmaIntro es'
modalPos (PosIndexIntro l meta) = return $ ValueIndexIntro l meta
modalPos (PosDownIntro e) = do
  e' <- modalNeg e
  modalBoxIntroPiIntro [] e'
  -- return $ SSPosBoxIntroPiIntro [] e'

-- modalNeg :: SSNeg -> WithEnv Comp
-- modalNeg (SSNegPiElimBoxElim fun args) = do
--   fun' <- modalPos fun
--   args' <- mapM modalPos args
--   return $ CompPiElimBoxElim fun' args'
--   -- tmp <- newNameWith "tmp"
--   -- bindLet [(tmp, fun')] $ CompPiElimBoxElim tmp args'
-- modalNeg (SSNegConstElim x es) = do
--   es' <- mapM modalPos es
--   xs <- mapM (const (newNameWith "arg")) es
--   bindLet (zip xs es') $ CompConstElim x xs
-- supplySNeg :: Neg -> WithEnv SSNeg
-- supplySNeg lam@(NegPiIntro _ _) = do
--   let (args, body) = toNegPiIntroSeq lam
--   body' <- supplySNeg body
--   let fvs = filter (`notElem` args) $ varSSNeg body'
--   return $
--     SSNegPiElimBoxElim
--       (SSPosBoxIntroPiIntro (fvs ++ args) body')
--       (map SSPosVar fvs)
-- supplySNeg app@(NegPiElim _ _) = do
--   let (fun, args) = toNegPiElimSeq app
--   fun' <- supplySNeg fun
--   args' <- mapM supplySPos args
--   commPiElim fun' args'
-- supplySNeg (NegSigmaElim e1 xs e2) = do
--   e1' <- supplySPos e1
--   e2' <- supplySNeg e2
--   return $ SSNegSigmaElim e1' xs e2'
-- supplySNeg (NegIndexElim e branchList) = do
--   let (labelList, es) = unzip branchList
--   es' <- mapM supplySNeg es
--   e' <- supplySPos e
--   return $ SSNegIndexElim e' (zip labelList es')
-- supplySNeg (NegUpIntro v) = do
--   v' <- supplySPos v
--   return $ SSNegUpIntro v'
-- supplySNeg (NegUpElim x e1 e2) = do
--   e1' <- supplySNeg e1
--   e2' <- supplySNeg e2
--   return $ SSNegUpElim x e1' e2'
-- supplySNeg (NegDownElim e) = do
--   e' <- supplySPos e
--   return $ SSNegPiElimBoxElim e' []
-- supplySNeg (NegConstElim x es) = do
--   es' <- mapM supplySPos es
--   return $ SSNegConstElim x es'
modalNeg :: Neg -> WithEnv Comp
modalNeg lam@(NegPiIntro _ _) = do
  let (args, body) = toNegPiIntroSeq lam
  let fvs = filter (`notElem` args) $ varNeg body
  body' <- modalNeg body
  -- let fvs = filter (`notElem` args) $ varSSNeg body'
  v <- modalBoxIntroPiIntro (fvs ++ args) body'
  return $ CompPiElimBoxElim v $ map ValueVar fvs
  -- return $
  --   SSNegPiElimBoxElim
  --     (SSPosBoxIntroPiIntro (fvs ++ args) body')
  --     (map SSPosVar fvs)
modalNeg app@(NegPiElim _ _) = do
  let (fun, args) = toNegPiElimSeq app
  fun' <- modalNeg fun
  args' <- mapM modalPos args
  commPiElim fun' args'
  -- fun' <- modalPos fun
  -- args' <- mapM modalPos args
  -- return $ CompPiElimBoxElim fun' args'
  -- tmp <- newNameWith "tmp"
  -- bindLet [(tmp, fun')] $ CompPiElimBoxElim tmp args'
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

-- translates (thunk (lam (x1 ... xn) e)).
modalBoxIntroPiIntro :: [Identifier] -> Comp -> WithEnv Value
modalBoxIntroPiIntro args body
  -- body' <- modalNeg body
 = do
  clsName <- newNameWith "cls"
  -- return $ ValueBoxIntroPiIntro args body'
  insModalEnv clsName args body
  -- insModalEnvFunc clsName args body'
  -- liftIO $ putStrLn $ "name == " ++ show clsName
  -- liftIO $ putStrLn $ "args == " ++ show args
  return $ ValueConst clsName

-- translates ((force v) @ v1 @ ... @ vn).
-- modalPiElimBoxElim :: Value -> [Pos] -> WithEnv Comp
-- modalPiElimBoxElim fun args = do
--   fun' <- modalPos fun
--   args' <- mapM modalPos args
--   return $ CompPiElimBoxElim fun' args'
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
