module Parse
  ( parse
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           System.Directory
import           System.FilePath
import           Text.Read                  (readMaybe)

import           Data.Basic
import           Data.Env
import           Data.Tree
import           Data.WeakTerm
import           Parse.Interpret
import           Parse.MacroExpand
import           Parse.Read
import           Parse.Rename

data Def =
  DefLet Identifier -- meta
         IdentifierPlus -- the `(x : t)` in `let (x : t) = e`
         WeakTerm -- the `e` in `let x = e`

parse :: String -> WithEnv WeakTerm
parse s = strToTree s >>= parse' >>= concatDefList

-- Parse the head element of the input list.
parse' :: [Tree] -> WithEnv [Def]
parse' [] = return []
parse' ((_ :< TreeNode [_ :< TreeAtom "notation", from, to]):as) =
  if not $ isSaneNotation from
    then lift $
         throwE
           "The '+'-suffixed name can be occurred only at the end of a list"
    else do
      modify (\e -> e {notationEnv = (from, to) : notationEnv e})
      parse' as
parse' ((_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom s]):as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  parse' as
parse' ((_ :< TreeNode ((_ :< TreeAtom "sortal"):(_ :< TreeAtom name):ts)):as) = do
  indexList <- mapM extractIdentifier ts
  insIndexEnv name indexList
  parse' as
parse' ((_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom pathString]):as) =
  case readMaybe pathString :: Maybe String of
    Nothing -> lift $ throwE "the argument of `include` must be a string"
    Just path -> do
      dirPath <- gets currentDir
      let nextPath = dirPath </> path
      b <- liftIO $ doesFileExist nextPath
      if not b
        then lift $ throwE $ "no such file: " ++ normalise nextPath
        else do
          content <- liftIO $ readFile nextPath
          let nextDirPath = dirPath </> takeDirectory path
          modify (\e -> e {currentDir = nextDirPath})
          includedDefList <- strToTree content >>= parse'
          modify (\e -> e {currentDir = dirPath})
          defList <- parse' as
          return $ includedDefList ++ defList
parse' ((_ :< TreeNode ((_ :< TreeAtom "statement"):as1)):as2) = do
  defList1 <- parse' as1
  defList2 <- parse' as2
  return $ defList1 ++ defList2
parse' ((_ :< TreeNode [_ :< TreeAtom "extern", _ :< TreeAtom name]):as)
  -- Declare external constants.
 = do
  modify (\e -> e {constantEnv = name : constantEnv e})
  parse' as
parse' ((meta :< TreeNode [_ :< TreeAtom "let", xt, e]):as) = do
  e' <- macroExpand e >>= interpret >>= rename
  (x, t) <- macroExpand xt >>= interpretIdentifierPlus
  t' <- rename t
  x' <- newNameWith x
  defList <- parse' as
  return $ DefLet meta (x', t') e' : defList
parse' (a:as)
  -- If the head element is not a special form, we interpret it as an ordinary term.
 = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta :< _) <- interpret e >>= rename
      name <- newNameWith "hole"
      t <- newHole
      defList <- parse' as
      return $ DefLet meta (name, t) e' : defList

isSpecialForm :: Tree -> Bool
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "notation", _, _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "sortal"):(_ :< TreeAtom _):_)) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "extern", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "statement"):_)) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "let", _, _]) = True
isSpecialForm _ = False

-- Represent the list of Defs in the target language, using `let`.
-- (Note that `let x := e1 in e2` can be represented as `(lam x e2) e1`.)
concatDefList :: [Def] -> WithEnv WeakTerm
concatDefList [] = do
  meta <- newNameWith "meta"
  return $ meta :< WeakTermSigmaIntro []
concatDefList (DefLet meta tu e:es) = do
  cont <- concatDefList es
  lamMeta <- newNameWith "meta"
  return $ meta :< WeakTermPiElim (lamMeta :< WeakTermPiIntro [tu] cont) [e]
