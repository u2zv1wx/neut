{-# LANGUAGE FlexibleInstances #-}

module Data.Env where

import Control.Monad.Except
import Control.Monad.State
import Data.List (elemIndex)
import System.Info

import Data.Basic
import Data.Code
import Data.Constraint
import Data.LLVM
import Data.PreTerm
import Data.Term
import Data.Tree

import qualified Data.Map.Strict as Map

import qualified Data.PQueue.Min as Q

import qualified Text.Show.Pretty as Pr

type ConstraintQueue = Q.MinQueue EnrichedConstraint

data Env =
  Env
    { count :: Int -- to generate fresh symbols
    , target :: Maybe Target
    , currentDir :: FilePath
    , keywordEnv :: [Identifier] -- list of reserved keywords
    , notationEnv :: [(TreePlus, TreePlus)] -- macro transformers
    , constantEnv :: [Identifier]
    , enumEnv :: [(Identifier, [Identifier])] -- [("choice", ["left", "right"]), ...]
    , nameEnv :: [(Identifier, Identifier)] -- [("foo", "foo.13"), ...]
    , weakTypeEnv :: Map.Map Identifier PreTermPlus -- var ~> typeof(var)
    , typeEnv :: Map.Map Identifier TermPlus
    , constraintEnv :: [PreConstraint] -- for type inference
    , substEnv :: [(Identifier, PreTermPlus)] -- metavar ~> beta-equivalent weakterm
    , codeEnv :: [(Identifier, ([Identifier], CodePlus))] -- f ~> thunk (lam (x1 ... xn) e)
    , llvmEnv :: [(Identifier, ([Identifier], LLVM))]
    }

initialEnv :: FilePath -> Env
initialEnv path =
  Env
    { count = 0
    , target = Nothing
    , notationEnv = []
    , keywordEnv = []
    , constantEnv = []
    , enumEnv = []
    , nameEnv = []
    , weakTypeEnv = Map.empty
    , typeEnv = Map.empty
    , codeEnv = []
    , llvmEnv = []
    , constraintEnv = []
    , substEnv = []
    , currentDir = path
    }

type WithEnv a = StateT Env (ExceptT String IO) a

evalWithEnv :: (Show a) => WithEnv a -> Env -> IO (Either String a)
evalWithEnv c env = do
  resultOrErr <- runExceptT (runStateT c env)
  case resultOrErr of
    Left err -> return $ Left err
    Right (result, _) -> return $ Right result

newName :: WithEnv Identifier
newName = do
  env <- get
  let i = count env
  modify (\e -> e {count = i + 1})
  return $ "-" ++ show i

newNameWith :: Identifier -> WithEnv Identifier
newNameWith s = do
  i <- newName
  let s' = s ++ i
  modify (\e -> e {nameEnv = (s, s') : nameEnv e})
  return s'

lookupWeakTypeEnv :: String -> WithEnv PreTermPlus
lookupWeakTypeEnv s = do
  mt <- lookupWeakTypeEnvMaybe s
  case mt of
    Just t -> return t
    Nothing -> throwError $ s ++ " is not found in the type environment."

lookupWeakTypeEnvMaybe :: String -> WithEnv (Maybe PreTermPlus)
lookupWeakTypeEnvMaybe s = do
  mt <- gets (Map.lookup s . weakTypeEnv)
  case mt of
    Nothing -> return Nothing
    Just t -> return $ Just t

lookupTypeEnv :: String -> WithEnv TermPlus
lookupTypeEnv s = do
  mt <- gets (Map.lookup s . typeEnv)
  case mt of
    Just t -> return t
    Nothing -> throwError $ s ++ " is not found in the type environment."

lookupNameEnv :: String -> WithEnv String
lookupNameEnv s = do
  ms <- lookupNameEnvMaybe s
  case ms of
    Just s' -> return s'
    Nothing -> throwError $ "undefined variable: " ++ show s

lookupNameEnvMaybe :: String -> WithEnv (Maybe String)
lookupNameEnvMaybe s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return $ Just s'
    Nothing -> return Nothing

lookupSubstEnv :: Identifier -> WithEnv (Maybe PreTermPlus)
lookupSubstEnv i = do
  senv <- gets substEnv
  return $ lookup i senv

insWeakTypeEnv :: Identifier -> PreTermPlus -> WithEnv ()
insWeakTypeEnv i t =
  modify (\e -> e {weakTypeEnv = Map.insert i t (weakTypeEnv e)})

insCodeEnv :: Identifier -> [Identifier] -> CodePlus -> WithEnv ()
insCodeEnv name args e =
  modify (\env -> env {codeEnv = (name, (args, e)) : codeEnv env})

insLLVMEnv :: Identifier -> [Identifier] -> LLVM -> WithEnv ()
insLLVMEnv funName args e =
  modify (\env -> env {llvmEnv = (funName, (args, e)) : llvmEnv env})

insEnumEnv :: Identifier -> [Identifier] -> WithEnv ()
insEnumEnv name enumList =
  modify (\e -> e {enumEnv = (name, enumList) : enumEnv e})

lookupKind :: Identifier -> WithEnv Identifier
lookupKind name = do
  env <- get
  lookupKind' name $ enumEnv env

lookupKind' :: Identifier -> [(Identifier, [Identifier])] -> WithEnv Identifier
lookupKind' i [] = throwError $ "no such enum-intro is defined: " ++ i
lookupKind' i ((j, ls):xs) =
  if i `elem` ls
    then return j
    else lookupKind' i xs

lookupEnumSet :: Identifier -> WithEnv [Identifier]
lookupEnumSet name = do
  eenv <- gets enumEnv
  case lookup name eenv of
    Nothing -> throwError $ "no such enum defined: " ++ show name
    Just ls -> return ls

getEnumNum :: Identifier -> WithEnv Int
getEnumNum label = do
  ienv <- gets enumEnv
  case (getEnumNum' label $ map snd ienv) of
    Nothing -> throwError $ "no such enum is defined: " ++ show label
    Just i -> return i

getEnumNum' :: Identifier -> [[Identifier]] -> Maybe Int
getEnumNum' _ [] = Nothing
getEnumNum' l (xs:xss) =
  case elemIndex l xs of
    Nothing -> getEnumNum' l xss
    Just i -> Just i

isDefinedEnum :: Identifier -> WithEnv Bool
isDefinedEnum name = do
  env <- get
  let labelList = join $ map snd $ enumEnv env
  return $ name `elem` labelList

isDefinedEnumName :: Identifier -> WithEnv Bool
isDefinedEnumName name = do
  env <- get
  let enumNameList = map fst $ enumEnv env
  return $ name `elem` enumNameList

insConstraintEnv :: PreTermPlus -> PreTermPlus -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

-- wrap :: a -> WithEnv (WeakMeta, a)
-- wrap a = do
--   meta <- newMeta
--   return (meta, a)
-- newHoleOfType :: WeakTermPlus -> WithEnv WeakTermPlus
-- newHoleOfType t = do
--   h <- newNameWith "hole"
--   m <- newMetaOfType t
--   return (m, WeakTermZeta h)
-- newMetaOfType :: WeakTermPlus -> WithEnv WeakMeta
-- newMetaOfType t = do
--   ref <- newWeakTermRef $ Just t
--   return $ WeakMetaNonTerminal ref Nothing
getTarget :: WithEnv Target
getTarget = do
  mtarget <- gets target
  case mtarget of
    Just t -> return t
    Nothing -> do
      currentOS <- getOS
      currentArch <- getArch
      return (currentOS, currentArch)

getOS :: WithEnv OS
getOS = do
  case os of
    "linux" -> return OSLinux
    "darwin" -> return OSDarwin
    s -> throwError $ "unsupported target os: " ++ show s

getArch :: WithEnv Arch
getArch = do
  case arch of
    "x86_64" -> return Arch64
    s -> throwError $ "unsupported target arch: " ++ show s

-- for debug
p :: String -> WithEnv ()
p s = liftIO $ putStrLn s

p' :: (Show a) => a -> WithEnv ()
p' s = liftIO $ putStrLn $ Pr.ppShow s

newDataUpsilonWith :: Identifier -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith name = newDataUpsilonWith' name emptyMeta

newDataUpsilonWith' :: Identifier -> Meta -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith' name m = do
  x <- newNameWith name
  return (x, (m, DataUpsilon x))
