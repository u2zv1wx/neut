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

import Elaborate
import Emit
import Exhaust

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
load :: String -> WithEnv [String]
load s = strToTree s >>= load' >>= concatDefList >>= process

-- Parse the head element of the input list.
load' :: [Tree] -> WithEnv [Def]
load' [] = return []
load' ((_ :< TreeNode [_ :< TreeAtom "notation", from, to]):as) =
  if not $ isSaneNotation from
    then E.lift $
         throwE
           "The '+'-suffixed name can be occurred only at the end of a list"
    else do
      modify (\e -> e {notationEnv = (from, to) : notationEnv e})
      load' as
load' ((_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom s]):as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  load' as
load' ((_ :< TreeNode ((_ :< TreeAtom "index"):(_ :< TreeAtom name):ts)):as) = do
  indexList <- mapM parseAtom ts
  insIndexEnv name indexList
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "include", _ :< TreeAtom pathString]):as) =
  case readMaybe pathString :: Maybe String of
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
          includedDefList <- strToTree content >>= load'
          modify (\e -> e {currentDir = dirPath})
          defList <- load' as
          return $ includedDefList ++ defList
load' ((meta :< TreeNode ((_ :< TreeAtom "module"):(_ :< TreeAtom moduleName):ts)):as)
  -- (module name statement-1 ... statement-n) is processed as follows:
  --   (1) process the list [statement-1, ..., statement-n], obtaining a defList.
  --   (1.1) let us write defList == [(name-1, e1), ..., (name-m, em)]
  --   (2) bind the tensor `(e1, ..., em)` to `name`.
  --   (3) update the moduleEnv, so that we can lookup the names name-i from the
  --   name of the tensor `name`.
 = do
  nenv <- gets notationEnv
  renv <- gets reservedEnv
  moduleDefList <- load' ts
  modify (\e -> e {notationEnv = nenv, reservedEnv = renv})
  xes <- join <$> mapM defToDefList moduleDefList
  moduleName' <- newNameWith moduleName
  modify (\e -> e {moduleEnv = (moduleName', xes) : moduleEnv e})
  let es = map snd xes
  boxMeta <- newNameWith "meta"
  let boxSigma = boxMeta :< NeutBoxIntro (meta :< NeutSigmaIntro es)
  defList <- load' as
  return $ DefLet meta (moduleName, moduleName') boxSigma : defList
load' ((meta :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom moduleName]):as)
  -- (use name) is essentially just a elimination of Sigma.
  -- Specifically, what (use name) does is:
  --   (1) lookup the moduleEnv, obtaining the list of names [name-1, ..., name-m].
  --   (2) create a sigma-decomposition `let (name:name-1, ..., name:name-m) = name`.
 = do
  moduleName' <- lookupNameEnv moduleName
  menv <- gets moduleEnv
  case lookup moduleName' menv of
    Nothing ->
      E.lift $
      throwE $
      "the module " ++
      moduleName ++ " is defined, but not registered in the module environment."
    Just xes -> do
      let (nameList, _) = unzip xes
      let nameList' = map (\s -> moduleName ++ ":" ++ s) nameList
      ns <- mapM newNameWith nameList'
      forM_ (zip nameList' ns) $ uncurry insNameEnv
      defList <- load' as
      return $ DefMod meta (moduleName, moduleName') ns : defList
load' ((_ :< TreeNode ((_ :< TreeAtom "statement"):as1)):as2)
  -- (statement stmt-1 ... stmt-n) is just a list of statements.
  -- This statement is useful when defining new statements using `notation`.
  -- For example, one may define `(import name path)` as:
  --   (statement (module name (include path)) (use name)).
 = do
  defList1 <- load' as1
  defList2 <- load' as2
  return $ defList1 ++ defList2
load' ((_ :< TreeNode [_ :< TreeAtom "ascription", _ :< TreeAtom name, t]):as) = do
  name' <- lookupNameEnv name
  t' <- macroExpand t >>= parse >>= rename
  insTypeEnv name' t'
  load' as
load' ((meta :< TreeNode [primMeta :< TreeAtom "primitive", _ :< TreeAtom name, t]):as)
  -- Declare external constants.
 = do
  let primName = "prim." ++ name
  primName' <- newNameWith primName
  name' <- newNameWith name
  t' <- macroExpand t >>= parse >>= rename
  constMeta <- newNameWith "meta"
  insTypeEnv name' t'
  insTypeEnv primName' $ constMeta :< NeutConst t'
  insTypeEnv name $ constMeta :< NeutConst t'
  defList <- load' as
  constElimMeta <- newNameWith "meta"
  primVarMeta <- newNameWith "meta"
  let constElim =
        constElimMeta :< NeutConstElim (primVarMeta :< NeutVar primName')
  defMeta <- newNameWith "meta"
  return $
    DefLet defMeta (primName, primName') (primMeta :< NeutConstIntro name) :
    DefLet meta (name, name') constElim : defList
load' ((meta :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom name, tbody]):as)
  -- `(let name body)` binds `body` to `name`.
 = do
  e <- macroExpand tbody >>= parse >>= rename
  name' <- newNameWith name
  defList <- load' as
  return $ DefLet meta (name, name') e : defList
load' (a:as)
  -- If the head element is not a special form, we interpret it as an ordinary term.
 = do
  e <- macroExpand a
  if isSpecialForm e
    then load' $ e : as
    else do
      e'@(meta :< _) <- parse e >>= rename
      name <- newNameWith "hole"
      defList <- load' as
      return $ DefLet meta (name, name) e' : defList

defToDefList :: Def -> WithEnv [(Identifier, Neut)]
defToDefList (DefLet _ (name, _) e) = return [(name, e)]
defToDefList (DefMod _ (name, name') _) = do
  menv <- gets moduleEnv
  case lookup name' menv of
    Nothing -> E.lift $ throwE $ "no such module: " ++ name
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
  return $ meta :< NeutIndexIntro (IndexLabel "unit")
concatDefList [DefLet _ _ e] = return e
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
  unboxMeta <- newNameWith "meta"
  let v = unboxMeta :< NeutBoxElim (meta :< NeutVar name')
  return $ sigMeta :< NeutSigmaElim v xs cont

process :: Neut -> WithEnv [String]
process e = do
  elaborate "main" e >>= nonRecReduce >>= exhaust >>= insWeakTermEnv "main"
  polarize
  modalize
  virtualize
  assemblize
  emit
