module Load
  ( load
  ) where

import qualified Control.Monad.Except as E
import Control.Monad.Identity
import Control.Monad.State hiding (lift)
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import Data.IORef

import Asm
import Data

import Emit
import Exhaust
import Infer
import Lift
import Macro
import Modal
import Parse
import Polarize
import Read
import Rename
import Virtual

import Reduce

import qualified Text.Show.Pretty as Pr

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
load' ((meta :< TreeNode [primMeta :< TreeAtom "primitive", _ :< TreeAtom name, t]):as) = do
  t' <- macroExpand t >>= parse >>= rename
  constNameWith name
  defList <- load' as
  return $ (meta, name, primMeta :< NeutConst name t') : defList
load' ((meta :< TreeNode [_ :< TreeAtom "definition", _ :< TreeAtom name, tbody]):as) = do
  e <- macroExpand tbody >>= parse >>= rename
  name' <- newNameWith name
  defList <- load' as
  return $ (meta, name', e) : defList
load' (a:as) = do
  e@(meta :< _) <- macroExpand a >>= parse >>= rename
  name <- newNameWith "hole"
  defList <- load' as
  return $ (meta, name, e) : defList

concatDefList :: [(Identifier, Identifier, Neut)] -> WithEnv Neut
concatDefList [] = do
  meta <- newNameWith "meta"
  return $ meta :< NeutIndexIntro (IndexLabel "unit")
concatDefList [(_, _, e)] = return e
concatDefList ((meta, name, e):es) = do
  cont <- concatDefList es
  h <- newNameWith "any"
  let hole = meta :< NeutHole h
  return $ meta :< NeutPiElim (meta :< NeutPiIntro (name, hole) cont) e

process :: Neut -> WithEnv ()
process e = do
  e' <- check "main" e >>= nonRecReduce
  c'' <- exhaust e' >>= lift
  insWeakTermEnv "main" c''
  polarize
  modal
  virtual
  asmCodeEnv
  emit
