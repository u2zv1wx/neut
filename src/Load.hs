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

-- import Lift
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

load :: String -> WithEnv [String]
load s = toDefList s >>= concatDefList >>= process

load' :: [Tree] -> WithEnv [Def]
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
load' ((meta :< TreeNode ((_ :< TreeAtom "module"):(_ :< TreeAtom moduleName):ts)):as) = do
  moduleDefList <- load' ts
  xes <- join <$> mapM defToDefList moduleDefList
  moduleName' <- newNameWith moduleName
  modify (\e -> e {moduleEnv = (moduleName', xes) : moduleEnv e})
  let es = map snd xes
  boxMeta <- newNameWith "meta"
  let boxSigma = boxMeta :< NeutBoxIntro (meta :< NeutSigmaIntro es)
  defList <- load' as
  return $ DefLet meta (moduleName, moduleName') boxSigma : defList
load' ((meta :< TreeNode [_ :< TreeAtom "use", _ :< TreeAtom moduleName]):as) = do
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
      ns <- mapM (newNameWith . (\s -> moduleName ++ ":" ++ s)) nameList
      defList <- load' as
      return $ DefMod meta (moduleName, moduleName') ns : defList
load' ((meta :< TreeNode [primMeta :< TreeAtom "primitive", _ :< TreeAtom name, t]):as) = do
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
  -- return $ DefLet meta (name, name) (primMeta :< NeutConst name t') : defList
load' ((meta :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom name, tbody]):as) = do
  e <- macroExpand tbody >>= parse >>= rename
  name' <- newNameWith name
  defList <- load' as
  return $ DefLet meta (name, name') e : defList
load' (a:as) = do
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
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "primitive", _ :< TreeAtom _, _]) =
  True
isSpecialForm (_ :< TreeNode [_ :< TreeAtom "let", _ :< TreeAtom _, _]) = True
isSpecialForm _ = False

toDefList :: String -> WithEnv [Def]
toDefList s = strToTree s >>= load'

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
  check "main" e >>= nonRecReduce >>= exhaust >>= insWeakTermEnv "main"
  polarize
  -- penv <- gets polEnv
  -- liftIO $ putStrLn $ Pr.ppShow penv
  -- liftIO $ putStrLn "-----------------------"
  modalize
  -- menv <- gets modalEnv
  -- liftIO $ putStrLn $ Pr.ppShow menv
  virtualize
  -- cenv <- gets codeEnv
  -- liftIO $ putStrLn $ Pr.ppShow cenv
  assemblize
  emit

data Def
  = DefLet Identifier
           (Identifier, Identifier)
           Neut
  | DefMod Identifier
           (Identifier, Identifier)
           [Identifier]
  deriving (Show)
