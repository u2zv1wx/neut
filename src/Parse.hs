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
import           Data.Neut
import           Data.Tree
import           Parse.Interpret
import           Parse.MacroExpand
import           Parse.Read
import           Parse.Rename

-- Def is essentially just a correspondence from name to term.
data Def
  = DefLet Identifier -- meta
           (Identifier, Identifier) -- (name, alpha-converted name)
           Neut -- content  (the `e` in `let x = e in ...`)
  -- a module is just a tensor of its contents.
  -- DefMod can be understood as `let x = (f1, ..., fn) in ...`.
  -- The `fi`s are the third argument of DefMod.
  | DefMod Identifier -- metaa
           (Identifier, Identifier) -- (name, alpha-converted name)
           [Identifier] -- list of the names of the contents
  deriving (Show)

-- Given a content of a file, translate it into the list of corresponding S-expressions
-- using `strToTree`. Then parse them into the list of definitions (updating the
-- internal state of the compiler). After that, concatenate the list of definitions,
-- obtaining a term. Finally, process the resulting term using `process`.
parse :: String -> WithEnv Neut
parse s = strToTree s >>= parse' >>= concatDefList

-- parse s = strToTree s >>= parse' >>= concatDefList >>= process
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
parse' ((_ :< TreeNode ((_ :< TreeAtom "index"):(_ :< TreeAtom name):ts)):as) = do
  indexList <- mapM interpretAtom ts
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
parse' ((meta :< TreeNode ((_ :< TreeAtom "module"):(_ :< TreeAtom moduleName):ts)):as)
  -- (module name statement-1 ... statement-n) is processed as follows:
  --   (1) process the list [statement-1, ..., statement-n], obtaining a defList.
  --   (1.1) let us write defList == [(name-1, e1), ..., (name-m, em)]
  --   (2) bind the tensor `(e1, ..., em)` to `name`.
  --   (3) update the moduleEnv, so that we can lookup the names name-i from the
  --   name of the tensor `name`.
 = do
  nenv <- gets notationEnv
  renv <- gets reservedEnv
  moduleDefList <- parse' ts
  modify (\e -> e {notationEnv = nenv, reservedEnv = renv})
  xes <- join <$> mapM defToDefList moduleDefList
  moduleName' <- newNameWith moduleName
  modify (\e -> e {moduleEnv = (moduleName', xes) : moduleEnv e})
  let es = map snd xes
  defList <- parse' as
  return $
    DefLet meta (moduleName, moduleName') (meta :< NeutSigmaIntro es) : defList
parse' ((meta :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom moduleName]):as)
  -- (use name) is essentially just a elimination of Sigma.
  -- Specifically, what (use name) does is:
  --   (1) lookup the moduleEnv, obtaining the list of names [name-1, ..., name-m].
  --   (2) create a sigma-decomposition `let (name:name-1, ..., name:name-m) = name`.
 = do
  moduleName' <- lookupNameEnv moduleName
  menv <- gets moduleEnv
  case lookup moduleName' menv of
    Nothing ->
      lift $
      throwE $
      "the module " ++
      moduleName ++ " is defined, but not registered in the module environment."
    Just xes -> do
      let (nameList, _) = unzip xes
      let nameList' = map (\s -> moduleName ++ ":" ++ s) nameList
      ns <- mapM newNameWith nameList'
      forM_ (zip nameList' ns) $ uncurry insNameEnv
      defList <- parse' as
      return $ DefMod meta (moduleName, moduleName') ns : defList
parse' ((_ :< TreeNode ((_ :< TreeAtom "statement"):as1)):as2)
  -- (statement stmt-1 ... stmt-n) is just a list of statements.
  -- This statement is useful when defining new statements using `notation`.
  -- For example, one may define `(import name path)` as:
  --   (statement (module name (include path)) (use name)).
 = do
  defList1 <- parse' as1
  defList2 <- parse' as2
  return $ defList1 ++ defList2
parse' ((_ :< TreeNode [_ :< TreeAtom "ascription", _ :< TreeAtom name, t]):as) = do
  name' <- lookupNameEnv name
  t' <- macroExpand t >>= interpret >>= rename
  insTypeEnv name' t'
  parse' as
parse' ((_ :< TreeNode [_ :< TreeAtom "primitive", _ :< TreeAtom name, t]):as)
  -- Declare external constants.
  -- e.g. (primitive core.i64.add (arrow i64 i64 i64))
 = do
  t' <- macroExpand t >>= interpret >>= rename
  insTypeEnv name t'
  modify (\e -> e {constantEnv = name : constantEnv e})
  parse' as
parse' ((meta :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom name, tbody]):as)
  -- `(let name body)` binds `body` to `name`.
 = do
  e <- macroExpand tbody >>= interpret >>= rename
  name' <- newNameWith name
  defList <- parse' as
  return $ DefLet meta (name, name') e : defList
parse' (a:as)
  -- If the head element is not a special form, we interpret it as an ordinary term.
 = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta :< _) <- interpret e >>= rename
      name <- newNameWith "hole"
      defList <- parse' as
      return $ DefLet meta (name, name) e' : defList

defToDefList :: Def -> WithEnv [(Identifier, Neut)]
defToDefList (DefLet _ (name, _) e) = return [(name, e)]
defToDefList (DefMod _ (name, name') _) = do
  menv <- gets moduleEnv
  case lookup name' menv of
    Nothing -> lift $ throwE $ "no such module: " ++ name
    Just es -> return es

isSpecialForm :: Tree -> Bool
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "notation", _, _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "index"):(_ :< TreeAtom _):_)) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "module", _ :< TreeAtom _, _]) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "primitive", _ :< TreeAtom _, _]) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "ascription", _ :< TreeAtom _, _]) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "statement", _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom _, _]) = True
isSpecialForm _ = False

-- Represent the list of Defs in the target language, using `let`.
-- (Note that `let x := e1 in e2` can be represented as `(lam x e2) e1`.)
concatDefList :: [Def] -> WithEnv Neut
concatDefList [] = do
  meta <- newNameWith "meta"
  return $ meta :< NeutSigmaIntro []
concatDefList [DefLet _ (_, _) e] = return e
concatDefList (DefLet meta (_, name') e:es) = do
  cont <- concatDefList es
  h <- newNameWith "any"
  holeMeta <- newNameWith "meta"
  let hole = holeMeta :< NeutHole h
  lamMeta <- newNameWith "meta"
  return $ meta :< NeutPiElim (lamMeta :< NeutPiIntro (name', hole) cont) e
concatDefList (DefMod sigMeta (_, name') xs:es) = do
  cont <- concatDefList es
  meta <- newNameWith "meta"
  return $ sigMeta :< NeutSigmaElim xs (meta :< NeutVar name') cont
