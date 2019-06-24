-- This module translates the content of file using `strToTree`, and
-- update the state of the compiler according to the head element of the
-- resulting list of S-expressions. After parseing all the S-expressions
-- in the list, this module concatenates all the definitions in the tree in some
-- appropriate way, obtaining a term.
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
         WeakUpsilonPlus -- the `x` in `let x = e`
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
parse' ((_ :< TreeNode ((_ :< TreeAtom "module"):(_ :< TreeAtom moduleName):ss)):as) = do
  menv <- gets moduleEnv
  modify (\env -> env {moduleEnv = menv ++ [moduleName]})
  defList1 <- parse' ss
  modify (\env -> env {moduleEnv = menv})
  defList2 <- parse' as
  return $ defList1 ++ defList2
parse' ((_ :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom moduleName]):as) = do
  modify (\env -> env {prefixEnv = moduleName : prefixEnv env})
  parse' as
parse' ((_ :< TreeNode [_ :< TreeAtom "unuse", _ :< TreeAtom moduleName]):as) = do
  modify (\env -> env {prefixEnv = filter (/= moduleName) $ prefixEnv env})
  parse' as
parse' ((_ :< TreeNode ((_ :< TreeAtom "statement"):as1)):as2)
  -- (statement stmt-1 ... stmt-n) is just a list of statements.
  -- This statement is useful when defining new statements using `notation`.
  -- For example, one may define `(import name path)` as:
  --   (statement (module name (include path)) (use name)).
 = do
  defList1 <- parse' as1
  defList2 <- parse' as2
  return $ defList1 ++ defList2
parse' ((_ :< TreeNode [_ :< TreeAtom "extern", _ :< TreeAtom name]):as)
  -- Declare external constants.
 = do
  modify (\e -> e {constantEnv = name : constantEnv e})
  parse' as
parse' ((meta :< TreeNode [_ :< TreeAtom "let", tsu, e]):as) = do
  e' <- macroExpand e >>= interpret >>= rename
  (t, (s, x)) <- macroExpand tsu >>= interpretUpsilonPlus
  t' <- rename t
  s' <- renameSortal s
  x' <- nameInModule x >>= newNameWith
  defList <- parse' as
  return $ DefLet meta (t', (s', x')) e' : defList
parse' (a:as)
  -- If the head element is not a special form, we interpret it as an ordinary term.
 = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta :< _) <- interpret e >>= rename
      name <- newNameWith "hole"
      name' <- nameInModule name
      s <- newSortalHole
      t <- newHole
      defList <- parse' as
      return $ DefLet meta (t, (s, name')) e' : defList

isSpecialForm :: Tree -> Bool
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "notation", _, _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "sortal"):(_ :< TreeAtom _):_)) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "module"):(_ :< TreeAtom _):_)) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "unuse", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "extern", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "statement"):_)) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "let", _, _]) = True
isSpecialForm _ = False

newCartesian :: WithEnv WeakSortal
newCartesian = do
  c <- newNameWith "cartesian"
  m <- newNameWith "meta"
  return $ WeakSortalTerm (m :< WeakTermEpsilonIntro (LiteralLabel c))

newSortalHole :: WithEnv WeakSortal
newSortalHole = do
  h <- newNameWith "hole"
  m <- newNameWith "meta"
  return $ WeakSortalTerm (m :< WeakTermHole h)

-- Represent the list of Defs in the target language, using `let`.
-- (Note that `let x := e1 in e2` can be represented as `(lam x e2) e1`.)
concatDefList :: [Def] -> WithEnv WeakTerm
concatDefList [] = do
  meta <- newNameWith "meta"
  s <- newCartesian
  return $ meta :< WeakTermSigmaIntro s []
concatDefList (DefLet meta tu e:es) = do
  cont <- concatDefList es
  lamMeta <- newNameWith "meta"
  sc <- newCartesian
  return $
    meta :< WeakTermPiElim sc (lamMeta :< WeakTermPiIntro sc [tu] cont) [e]
