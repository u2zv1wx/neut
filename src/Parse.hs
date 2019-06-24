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

-- Def is essentially just a correspondence from name to term.
data Def
  -- (let s (A x) e)
  = DefLet Identifier -- meta
           WeakUpsilonPlus
           WeakTerm -- content  (the `e` in `let x = e in ...`)
  -- (module x e1 ... en)
  -- a module is just a tensor of its contents.
  -- DefMod can be understood as `let x = (f1, ..., fn) in ...`.
  -- The `fi`s are the third argument of DefMod.
  | DefMod Identifier -- meta
           WeakUpsilon
           [WeakUpsilonPlus] -- list of the names of the contents

-- Given a content of a file, translate it into the list of corresponding S-expressions
-- using `strToTree`. Then parse them into the list of definitions (updating the
-- internal state of the compiler). After that, concatenate the list of definitions,
-- obtaining a term. Finally, process the resulting term using `process`.
parse :: String -> WithEnv WeakTerm
parse s = strToTree s >>= parse' >>= concatDefList >>= rename

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
parse' ((_ :< TreeNode ((_ :< TreeAtom "sortal"):(_ :< TreeAtom name):ts)):as) = do
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
  tues <- join <$> mapM defToDefList moduleDefList
  s <- newCartesian
  modify (\e -> e {moduleEnv = (moduleName, (s, tues)) : moduleEnv e})
  let es = map snd tues
  let tus = map fst tues
  typeMeta <- newNameWith "meta"
  let t = typeMeta :< WeakTermSigma s tus
  defList <- parse' as
  return $
    DefLet meta (t, (s, moduleName)) (meta :< WeakTermSigmaIntro s es) : defList
parse' ((meta :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom moduleName]):as)
  -- (use name) is essentially just a elimination of Sigma.
  -- Specifically, what (use name) does is:
  --   (1) lookup the moduleEnv, obtaining the list of names [name-1, ..., name-m].
  --   (2) create a sigma-decomposition `let (name.name-1, ..., name.name-m) = name`.
 = do
  menv <- gets moduleEnv
  case lookup moduleName menv of
    Nothing ->
      lift $
      throwE $
      "the module " ++
      moduleName ++ " is defined, but not registered in the module environment."
    Just (smod, tues) -> do
      let tus = map fst tues
      let tus' = map (\(t, (s, x)) -> (t, (s, moduleName ++ "." ++ x))) tus
      defList <- parse' as
      return $ DefMod meta (smod, moduleName) tus' : defList
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
parse' ((meta :< TreeNode [_ :< TreeAtom "let", tsu, e]):as)
  -- (let tsu e)
  -- `(let name body)` binds `body` to `name`.
 = do
  tsu' <- macroExpand tsu >>= interpretUpsilonPlus
  e' <- macroExpand e >>= interpret
  defList <- parse' as
  return $ DefLet meta tsu' e' : defList
parse' (a:as)
  -- If the head element is not a special form, we interpret it as an ordinary term.
 = do
  e <- macroExpand a
  if isSpecialForm e
    then parse' $ e : as
    else do
      e'@(meta :< _) <- interpret e
      name <- newNameWith "hole"
      s <- newSortalHole
      t <- newHole
      defList <- parse' as
      return $ DefLet meta (t, (s, name)) e' : defList

defToDefList :: Def -> WithEnv [(WeakUpsilonPlus, WeakTerm)]
defToDefList (DefLet _ tu e) = return [(tu, e)]
defToDefList (DefMod _ (_, name) _) = do
  menv <- gets moduleEnv
  case lookup name menv of
    Nothing         -> lift $ throwE $ "no such module: " ++ name
    Just (_, tsues) -> return tsues -- FIXME: Modify name?

isSpecialForm :: Tree -> Bool
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "notation", _, _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode ((_ :< TreeAtom "sortal"):(_ :< TreeAtom _):_)) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "module", _ :< TreeAtom _, _]) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "constant", _ :< TreeAtom _, _]) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "statement", _]) = True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom _, _]) = True
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
concatDefList [DefLet _ (_, _) e] = return e
concatDefList (DefLet meta (t, (s, x)) e:es) = do
  cont <- concatDefList es
  lamMeta <- newNameWith "meta"
  sc <- newCartesian
  return $
    meta :<
    WeakTermPiElim sc (lamMeta :< WeakTermPiIntro sc [(t, (s, x))] cont) [e]
concatDefList (DefMod sigMeta (s, x) xs:es) = do
  cont <- concatDefList es
  meta <- newNameWith "meta"
  return $
    sigMeta :< WeakTermSigmaElim s xs (meta :< WeakTermUpsilon (s, x)) cont
