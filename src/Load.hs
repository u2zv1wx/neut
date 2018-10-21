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

import System.Directory
import System.FilePath

import Text.Read (readMaybe)

import qualified Text.Show.Pretty as Pr

load :: String -> WithEnv ()
load s = toDefList s >>= concatDefList >>= process

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
load' ((_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom s]):as) =
  case readMaybe s :: Maybe String of
    Nothing -> E.lift $ throwE "the argument of `include` must be a string"
    Just path -> do
      dirPath <- gets currentDir
      let nextPath = dirPath </> path
      b <- liftIO $ doesFileExist nextPath
      if not b
        then E.lift $ throwE $ "no such file: " ++ normalise nextPath
        else do
          content <- liftIO $ readFile nextPath
          let nextDirPath = dirPath </> takeDirectory path
          modify (\e -> e {currentDir = nextDirPath})
          includedDefList <- toDefList content
          modify (\e -> e {currentDir = dirPath})
          defList <- load' as
          return $ includedDefList ++ defList
load' ((meta :< TreeNode [primMeta :< TreeAtom "primitive", _ :< TreeAtom name, t]):as) = do
  t' <- macroExpand t >>= parse >>= rename
  constNameWith name
  defList <- load' as
  return $ (meta, name, primMeta :< NeutConst name t') : defList
load' ((meta :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom name, tbody]):as) = do
  e <- macroExpand tbody >>= parse >>= rename
  name' <- newNameWith name
  defList <- load' as
  return $ (meta, name', e) : defList
load' (a:as) = do
  e <- macroExpand a
  if isSpecialForm e
    then load' $ e : as
    else do
      e'@(meta :< _) <- parse e >>= rename
      name <- newNameWith "hole"
      defList <- load' as
      return $ (meta, name, e') : defList

isSpecialForm :: Tree -> Bool
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "notation", _, _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "index"):(_ :< TreeAtom _):_)) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "primitive", _ :< TreeAtom _, _]) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom _, _]) = True
isSpecialForm _ = False

toDefList :: String -> WithEnv [(Identifier, Identifier, Neut)]
toDefList s = strToTree s >>= load'

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
  check "main" e >>= nonRecReduce >>= exhaust >>= insWeakTermEnv "main"
  polarize
  modalize
  virtualize
  assemblize
  emit
