module Load
  ( load
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data.IORef

import           Asm
import           Data
import           Emit
import           Infer
import           Lift
import           Macro
import           Parse
import           Polarize
import           Read
import           Rename
import           Virtual

import qualified Text.Show.Pretty           as Pr

load :: String -> WithEnv ()
load s = do
  astList <- strToTree s
  load' astList

load' :: [Tree] -> WithEnv ()
load' [] = return ()
load' ((_ :< TreeNode [_ :< TreeAtom "notation", from, to]):as) = do
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom s]):as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "value", _ :< TreeAtom s, _ :< TreeNode tps, tp]):as) = do
  mts <- mapM parseNodeTypeArg tps
  mt <- parseType tp
  (mts', mt') <- renameNodeType mts mt
  ts <- polarizeTypeArg mts'
  t <- polarizeType mt'
  case t of
    TypeValueType t@(ValueTypeNode k _) -> do
      modify (\e -> e {valueEnv = (s, ts, t) : valueEnv e})
      insWTEnv s (weakenValueType t)
      insConstructorEnv k s
      load' as
    TypeValueType t@(ValueTypeUniv _) -> do
      modify (\e -> e {valueEnv = (s, ts, t) : valueEnv e})
      insWTEnv s (weakenValueType t)
      load' as
    _ ->
      lift $
      throwE $
      "the codomain of value type " ++ show s ++ " must be universe or node"
load' (a:as) = do
  a' <- macroExpand a
  e <- parseTerm a'
  e' <- rename e
  check e'
  env <- get
  let wtenv = weakTypeEnv env
  polarizeTypeEnv wtenv
  e'' <- polarize e'
  case e'' of
    TermValue _ -> do
      liftIO $ putStrLn "the type of main term must be negative"
    TermComp c -> do
      liftedC <- liftC c
      initializeLinkRegister
      initializeReturnRegister
      i <- newNameWith "main"
      setScope i
      insEmptyCodeEnv i
      c' <- virtualC liftedC >>= liftIO . newIORef
      insCodeEnv' i c'
      -- env <- get
      -- mainCode <- lookupFunEnv i >>= liftIO . readIORef
      -- liftIO $ putStrLn "===========FUNENV======"
      -- liftIO $ putStrLn $ Pr.ppShow $ funEnv env
      -- liftIO $ putStrLn "starting liveness analysis"
      -- liftIO $ putStrLn $ "mainCode : \n" ++ Pr.ppShow mainCode
      -- liftIO $ putStrLn $ "c'' : \n" ++ Pr.ppShow mainCode'
      -- regAlloc 32
      -- updateCodeEnv i mainCode'
      -- asmEmit
      -- emit
      env <- get
      liftIO $ putStrLn $ Pr.ppShow (codeEnv env)
  load' as
