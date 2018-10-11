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
import           Infer
import           Lift
import           Macro
import           Parse
import           Polarize
import           Read
import           Rename
import           Virtual

import           Reduce

import qualified Text.Show.Pretty           as Pr

load :: String -> WithEnv ()
load s = do
  astList <- strToTree s
  defList <- load' astList
  e <- concatDefList defList
  -- liftIO $ putStrLn $ Pr.ppShow e
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
  tmp <- macroExpand tbody >>= parse
  -- liftIO $ putStrLn $ Pr.ppShow tmp
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
concatDefList ((meta, name, e):es) = do
  cont <- concatDefList es
  h <- newNameWith "any"
  let hole = meta :< NeutHole h
  return $ meta :< NeutPiElim (meta :< NeutPiIntro (name, hole) cont) e

process :: Neut -> WithEnv ()
process e = do
  e' <- check mainLabel e
  -- p <- exhaust e' >>= lift
  -- liftIO $ putStrLn $ Pr.ppShow p
  -- c' <- exhaust e' >>= expand >>= lift >>= polarizeNeg >>= virtualNeg
  c'' <- exhaust e' >>= lift
  -- c'' <- exhaust e' >>= lift >>= polarizeNeg
  insWeakTermEnv mainLabel c''
  wtenv <- gets weakTermEnv
  -- liftIO $ putStrLn "lifted."
  forM_ wtenv $ \(name, e) ->
    polarizeNeg e >>= reduceNeg >>= virtualNeg >>= insCodeEnv name []
    -- e' <- polarizeNeg e
    -- e'' <- reduceNeg e'
    -- liftIO $ putStrLn $ "name: " ++ name
    -- liftIO $ putStrLn $ Pr.ppShow e''
  -- liftIO $ putStrLn $ Pr.ppShow c''
  -- c' <- exhaust e' >>= lift >>= polarizeNeg >>= virtualNeg
  -- liftIO $ putStrLn $ Pr.ppShow c'
  -- insCodeEnv mainLabel [] c'
  -- ce <- gets codeEnv
  -- liftIO $ putStrLn $ Pr.ppShow ce
  asmCodeEnv
  -- liftIO $ putStrLn $ "asmCodeEnv."
  emitGlobalLabel mainLabel
  emit

mainLabel :: Identifier
mainLabel = "_main"
