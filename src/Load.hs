module Load
  ( load
  ) where

import qualified Control.Monad.Except       as E
import           Control.Monad.Identity
import           Control.Monad.State        hiding (lift)
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data.IORef

import           Asm
import           Data

import           Emit
import           Exhaust
import           Expand
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
load' ((_ :< TreeNode ((_ :< TreeAtom "index"):(_ :< TreeAtom name):ts)):as) = do
  indexList <- mapM parseAtom ts
  insIndexEnv name indexList
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "primitive", _ :< TreeAtom name, t]):as) = do
  e <- macroExpand t >>= parse >>= rename
  e' <- check name e
  t <- lookupTypeEnv' name
  case t of
    _ :< NeutBox (_ :< NeutUniv _) -> do
      insConstEnv name e'
      env <- get
      liftIO $ putStrLn $ Pr.ppShow (constEnv env)
      load' as
    _ -> error $ "the type of " ++ name ++ " is not univ"
load' (a:as) = do
  e <- macroExpand a >>= parse >>= rename
  liftIO $ putStrLn $ Pr.ppShow e
  e' <- check mainLabel e
  liftIO $ putStrLn $ Pr.ppShow e'
  lifted <- exhaust e' >>= lift
  liftIO $ putStrLn $ Pr.ppShow lifted
  tmp <- exhaust e' >>= lift >>= expand >>= polarize >>= toNeg
  liftIO $ putStrLn $ Pr.ppShow tmp
  c' <- exhaust e' >>= lift >>= expand >>= polarize >>= toNeg >>= virtualNeg
  -- liftIO $ putStrLn $ Pr.ppShow c'
  insCodeEnv mainLabel [] c'
  env <- get
  liftIO $ putStrLn $ Pr.ppShow (codeEnv env)
  asmCodeEnv
  emitGlobalLabel mainLabel
  emit
  -- env <- get
  -- liftIO $ putStrLn $ Pr.ppShow $ regEnv env
  load' as

mainLabel :: Identifier
mainLabel = "_main"
