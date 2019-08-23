{-# LANGUAGE FlexibleInstances #-}

module Data.Env where

-- import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef
import           Data.List                  (elemIndex)

import           Data.Basic
import           Data.Code
import           Data.Constraint
import           Data.LLVM
import           Data.Tree
import           Data.WeakCode
import           Data.WeakTerm

import qualified Data.Map.Strict            as Map

import qualified Data.PQueue.Min            as Q

type ConstraintQueue = Q.MinQueue EnrichedConstraint

data Env = Env
  { count :: Int -- to generate fresh symbols
  , currentDir :: FilePath
  , reservedEnv :: [Identifier] -- list of reserved keywords
  , notationEnv :: [(Tree, Tree)] -- macro transformers
  , constantEnv :: [Identifier]
  , epsilonEnv :: [(Identifier, [Identifier])]
  , nameEnv :: [(Identifier, Identifier)] -- [("foo", "foo.13"), ...]
  , typeEnv :: Map.Map Identifier WeakTermPlus -- var ~> typeof(var)
  , constraintEnv :: [PreConstraint] -- for type inference
  , constraintQueue :: ConstraintQueue -- for (dependent) type inference
  , substEnv :: SubstWeakTerm -- metavar ~> beta-equivalent weakterm
  , polEnv :: [(Identifier, ([(Identifier, WeakDataPlus)], WeakCodePlus))] -- f ~> thunk (lam (x1 ... xn) e)
  , llvmEnv :: [(Identifier, ([Identifier], LLVM))]
  }

initialEnv :: FilePath -> Env
initialEnv path =
  Env
    { count = 0
    , notationEnv = []
    , reservedEnv = []
    , constantEnv = []
    , epsilonEnv = []
    , nameEnv = []
    , typeEnv = Map.empty
    , polEnv = []
    , llvmEnv = []
    , constraintEnv = []
    , constraintQueue = Q.empty
    , substEnv = []
    , currentDir = path
    }

type WithEnv a = StateT Env (ExceptT String IO) a

liftToWithEnv :: (IO a -> IO b) -> WithEnv a -> WithEnv b
liftToWithEnv f e = do
  e' <- e
  liftIO $ f (return e')

runWithEnv :: WithEnv a -> Env -> IO (Either String (a, Env))
runWithEnv c env = runExceptT (runStateT c env)

evalWithEnv :: (Show a) => WithEnv a -> Env -> IO (Either String a)
evalWithEnv c env = do
  resultOrErr <- runWithEnv c env
  case resultOrErr of
    Left err          -> return $ Left err
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

newNameOfType :: WeakTermPlus -> Identifier -> WithEnv Identifier
newNameOfType t s = do
  i <- newNameWith s
  insTypeEnv i t
  return i

lookupTypeEnv :: String -> WithEnv WeakTermPlus
lookupTypeEnv s = do
  mt <- lookupTypeEnvMaybe s
  case mt of
    Just t  -> return t
    Nothing -> lift $ throwE $ s ++ " is not found in the type environment."

lookupTypeEnvMaybe :: String -> WithEnv (Maybe WeakTermPlus)
lookupTypeEnvMaybe s = do
  mt <- gets (Map.lookup s . typeEnv)
  case mt of
    Nothing -> return Nothing
    Just t  -> return $ Just t

lookupNameEnv :: String -> WithEnv String
lookupNameEnv s = do
  ms <- lookupNameEnvMaybe s
  case ms of
    Just s' -> return s'
    Nothing -> lift $ throwE $ "undefined variable: " ++ show s

lookupNameEnvMaybe :: String -> WithEnv (Maybe String)
lookupNameEnvMaybe s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return $ Just s'
    Nothing -> return Nothing

insTypeEnv :: Identifier -> WeakTermPlus -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = Map.insert i t (typeEnv e)})

insPolEnv ::
     Identifier -> [(Identifier, WeakDataPlus)] -> WeakCodePlus -> WithEnv ()
insPolEnv name args e =
  modify (\env -> env {polEnv = (name, (args, e)) : polEnv env})

insLLVMEnv :: Identifier -> [Identifier] -> LLVM -> WithEnv ()
insLLVMEnv funName args e =
  modify (\env -> env {llvmEnv = (funName, (args, e)) : llvmEnv env})

insEpsilonEnv :: Identifier -> [Identifier] -> WithEnv ()
insEpsilonEnv name epsilonList =
  modify (\e -> e {epsilonEnv = (name, epsilonList) : epsilonEnv e})

lookupKind :: Literal -> WithEnv (Maybe Identifier)
lookupKind (LiteralInteger _) = return Nothing
lookupKind (LiteralFloat _) = return Nothing
lookupKind (LiteralLabel name) = do
  env <- get
  lookupKind' name $ epsilonEnv env

lookupKind' ::
     Identifier -> [(Identifier, [Identifier])] -> WithEnv (Maybe Identifier)
lookupKind' _ [] = return Nothing
lookupKind' i ((j, ls):xs) =
  if i `elem` ls
    then return $ Just j
    else lookupKind' i xs

lookupEpsilonSet :: Identifier -> WithEnv [Identifier]
lookupEpsilonSet name = do
  env <- get
  lookupEpsilonSet' name $ epsilonEnv env

lookupEpsilonSet' ::
     Identifier -> [(Identifier, [Identifier])] -> WithEnv [Identifier]
lookupEpsilonSet' name [] =
  lift $ throwE $ "no such epsilon defined: " ++ show name
lookupEpsilonSet' name ((_, ls):xs) =
  if name `elem` ls
    then return ls
    else lookupEpsilonSet' name xs

getEpsilonNum :: Identifier -> WithEnv (Maybe Int)
getEpsilonNum label = do
  ienv <- gets epsilonEnv
  return $ getEpsilonNum' label $ map snd ienv

getEpsilonNum' :: Identifier -> [[Identifier]] -> Maybe Int
getEpsilonNum' _ [] = Nothing
getEpsilonNum' l (xs:xss) =
  case elemIndex l xs of
    Nothing -> getEpsilonNum' l xss
    Just i  -> Just i

isDefinedEpsilon :: Identifier -> WithEnv Bool
isDefinedEpsilon name = do
  env <- get
  let labelList = join $ map snd $ epsilonEnv env
  return $ name `elem` labelList

isDefinedEpsilonName :: Identifier -> WithEnv Bool
isDefinedEpsilonName name = do
  env <- get
  let epsilonNameList = map fst $ epsilonEnv env
  return $ name `elem` epsilonNameList

insConstraintEnv :: WeakTermPlus -> WeakTermPlus -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

wrap :: a -> WithEnv (WeakMeta, a)
wrap a = do
  meta <- newMeta
  return (meta, a)

newHoleOfType :: WeakTermPlus -> WithEnv WeakTermPlus
newHoleOfType t = do
  h <- newNameWith "hole"
  m <- newMetaOfType t
  return (m, WeakTermZeta h)

newMeta :: WithEnv WeakMeta
newMeta = do
  t <- liftIO $ newIORef Nothing
  return $ WeakMetaNonTerminal (Ref t) Nothing

newMetaTerminal :: WeakMeta
newMetaTerminal = WeakMetaTerminal Nothing

newMetaOfType :: WeakTermPlus -> WithEnv WeakMeta
newMetaOfType t = do
  t' <- liftIO $ newIORef (Just t)
  return $ WeakMetaNonTerminal (Ref t') Nothing

toWeakMeta :: TreeMeta -> WithEnv WeakMeta
toWeakMeta m = do
  t <- liftIO $ newIORef Nothing
  return $ WeakMetaNonTerminal (Ref t) (treeMetaLocation m)
