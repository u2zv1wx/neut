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
  defList <- load' astList
  e <- concatDefList defList
  process e

load' :: [Tree] -> WithEnv [(Identifier, Identifier, Neut)]
load' [] = return []
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
load' ((meta :< TreeNode [_ :< TreeAtom "definition", _ :< TreeAtom name, tbody]):as) = do
  e <- macroExpand tbody >>= parse >>= rename
  name' <- newNameWith name
  defList <- load' as
  return $ (meta, name', e) : defList
load' (a:as) = do
  e <- macroExpand a >>= parse >>= rename
  -- liftIO $ putStrLn $ Pr.ppShow e
  let (meta :< _) = e
  name <- newNameWith "hole"
  defList <- load' as
  return $ (meta, name, e) : defList
  -- e' <- check mainLabel e
  -- -- liftIO $ putStrLn $ Pr.ppShow e'
  -- -- lifted <- exhaust e' >>= lift
  -- -- liftIO $ putStrLn $ Pr.ppShow lifted
  -- tmp <- exhaust e' >>= lift >>= expand >>= polarize >>= toNeg
  -- -- liftIO $ putStrLn $ Pr.ppShow tmp
  -- c' <- exhaust e' >>= lift >>= expand >>= polarize >>= toNeg >>= virtualNeg
  -- -- liftIO $ putStrLn $ Pr.ppShow c'
  -- insCodeEnv mainLabel [] c'
  -- env <- get
  -- -- liftIO $ putStrLn $ Pr.ppShow (codeEnv env)
  -- asmCodeEnv
  -- emitGlobalLabel mainLabel
  -- emit
  -- env <- get
  -- liftIO $ putStrLn $ Pr.ppShow $ regEnv env
  -- load' as

concatDefList :: [(Identifier, Identifier, Neut)] -> WithEnv Neut
concatDefList [] = do
  meta <- newNameWith "meta"
  return $ meta :< NeutIndexIntro (IndexLabel "unit")
concatDefList ((meta, name, e):es) = do
  cont <- concatDefList es
  h <- newNameWith "any"
  let hole = meta :< NeutHole h
  return $ meta :< NeutPiElim (meta :< NeutPiIntro (name, hole) cont) e

process :: Neut -> WithEnv ()
process e = do
  liftIO $ putStrLn $ Pr.ppShow e
  e' <- check mainLabel e
  c' <- exhaust e' >>= lift >>= expand >>= polarize >>= toNeg >>= virtualNeg
  -- liftIO $ putStrLn $ Pr.ppShow c'
  insCodeEnv mainLabel [] c'
  asmCodeEnv
  emitGlobalLabel mainLabel
  emit

mainLabel :: Identifier
mainLabel = "_main"
