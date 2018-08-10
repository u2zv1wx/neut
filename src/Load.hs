module Load
  ( load
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data.IORef

import           Data
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
  ts <- polarizeTypeArg mts' -- todo : check free var occurrence
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
  liftIO $ putStrLn $ Pr.ppShow a'
  e <- parseTerm a'
  liftIO $ putStrLn $ Pr.ppShow e
  e' <- rename e
  liftIO $ putStrLn $ Pr.ppShow e'
  check e'
  env <- get
  let wtenv = weakTypeEnv env
  tenv <- polarizeTypeEnv wtenv
  modify (\e -> e {typeEnv = tenv})
  e'' <- polarize e'
  case e'' of
    TermValue v -> do
      liftIO $ putStrLn $ Pr.ppShow v
      insEmptyFunEnv "main"
      setFunName "main"
      v' <- virtualV v
      liftIO $ putStrLn $ Pr.ppShow v'
      liftIO $ putStrLn "the type of main term must be negative"
    TermComp c -> do
      liftIO $ putStrLn $ Pr.ppShow c
      liftedC <- liftC c
      liftIO $ putStrLn $ Pr.ppShow liftedC
      insEmptyFunEnv "main"
      setFunName "main"
      c' <- virtualC liftedC
      liftIO $ putStrLn $ Pr.ppShow c'
      i <- newNameWith "main"
      cref <- liftIO $ newIORef c'
      insCodeEnv i cref
  load' as
