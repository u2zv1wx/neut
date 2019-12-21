module Parse
  ( parse
  ) where

import Control.Monad.Except
import Control.Monad.State
import System.Directory
import System.FilePath
import Text.Read (readMaybe)

import Data.Env
import Data.Tree
import Data.WeakTerm
import Parse.Interpret
import Parse.MacroExpand
import Parse.Read
import Parse.Rename

data Def =
  DefLet
    WeakMeta -- meta
    IdentifierPlus -- the `(x : t)` in `let (x : t) = e`
    WeakTermPlus -- the `e` in `let x = e`

parse :: String -> WithEnv WeakTermPlus
parse s = strToTree s >>= parse' >>= concatDefList

-- Parse the head element of the input list.
parse' :: [TreePlus] -> WithEnv [Def]
parse' [] = return []
parse' ((_, TreeNode [(_, TreeAtom "notation"), from, to]):as) =
  if not $ isSaneNotation from
    then throwError
           "The '+'-suffixed name can be occurred only at the end of a list"
    else do
      modify (\e -> e {notationEnv = (from, to) : notationEnv e})
      parse' as
parse' ((_, TreeNode [(_, TreeAtom "keyword"), (_, TreeAtom s)]):as) = do
  modify (\e -> e {keywordEnv = s : keywordEnv e})
  parse' as
parse' ((_, TreeNode ((_, TreeAtom "enum"):(_, TreeAtom name):ts)):as) = do
  indexList <- mapM extractIdentifier ts
  insEnumEnv name indexList
  parse' as
parse' ((_, TreeNode [(_, TreeAtom "include"), (_, TreeAtom pathString)]):as) =
  case readMaybe pathString :: Maybe String of
    Nothing -> throwError "the argument of `include` must be a string"
    Just path -> do
      dirPath <- gets currentDir
      let nextPath = dirPath </> path
      b <- liftIO $ doesFileExist nextPath
      if not b
        then throwError $ "no such file: " ++ normalise nextPath
        else do
          content <- liftIO $ readFile nextPath
          let nextDirPath = dirPath </> takeDirectory path
          modify (\e -> e {currentDir = nextDirPath})
          includedDefList <- strToTree content >>= parse'
          modify (\e -> e {currentDir = dirPath})
          defList <- parse' as
          return $ includedDefList ++ defList
parse' ((_, TreeNode ((_, TreeAtom "statement"):as1)):as2) = do
  defList1 <- parse' as1
  defList2 <- parse' as2
  return $ defList1 ++ defList2
parse' ((_, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom name)]):as)
  -- Declare external constants.
 = do
  modify (\e -> e {constantEnv = name : constantEnv e})
  parse' as
parse' ((_, TreeNode [(_, TreeAtom "let"), xt, e]):as) = do
  e' <- macroExpand e >>= interpret >>= rename
  (x, t) <- macroExpand xt >>= interpretIdentifierPlus
  t' <- rename t
  x' <- newNameWith x
  defList <- parse' as
  m <- newMeta
  return $ DefLet m (x', t') e' : defList
parse' (a:as)
  -- If the head element is not a special form, we interpret it as an ordinary term.
 = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta, _) <- interpret e >>= rename
      name <- newNameWith "hole"
      u <- wrap WeakTermTau
      t <- newHoleOfType u
      defList <- parse' as
      return $ DefLet meta (name, t) e' : defList

isSpecialForm :: TreePlus -> Bool
isSpecialForm (_, TreeNode [(_, TreeAtom "notation"), _, _]) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "keyword"), (_, TreeAtom _)]) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "enum"):(_, TreeAtom _):_)) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "include"), (_, TreeAtom _)]) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom _)]) = True
isSpecialForm (_, TreeNode ((_, TreeAtom "statement"):_)) = True
isSpecialForm (_, TreeNode [(_, TreeAtom "let"), _, _]) = True
isSpecialForm _ = False

-- Represent the list of Defs in the target language, using `let`.
-- (Note that `let x := e1 in e2` can be represented as `(lam x e2) e1`.)
concatDefList :: [Def] -> WithEnv WeakTermPlus
concatDefList [] = do
  let t = (WeakMetaTerminal Nothing, WeakTermEnum "top")
  m <- newMetaOfType t
  return (m, WeakTermEnumIntro "unit")
concatDefList (DefLet meta tu e:es) = do
  cont <- concatDefList es
  m <- newMeta
  return (meta, WeakTermPiElim (m, WeakTermPiIntro [tu] cont) [e])
