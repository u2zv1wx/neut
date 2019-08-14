{-# LANGUAGE FlexibleInstances #-}

module Data.Env where

import           Control.Comonad.Cofree
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.IORef
import           Data.List                  (elemIndex)

import           Data.Basic
import           Data.Constraint
import           Data.LLVM
import           Data.Polarized
import           Data.Term
import           Data.Tree
import           Data.WeakTerm

import qualified Data.Map.Strict            as Map

import qualified Data.PQueue.Min            as Q

type ConstraintQueue = Q.MinQueue EnrichedConstraint

data Env = Env
  { count           :: Int -- to generate fresh symbols
  , notationEnv     :: [(Tree, Tree)] -- macro transformers
  , reservedEnv     :: [Identifier] -- list of reserved keywords
  , constantEnv     :: [Identifier]
  , epsilonEnv      :: [(Identifier, [Identifier])]
  , nameEnv         :: [(Identifier, Identifier)] -- [("foo", "foo.13"), ...]
  , typeEnv         :: Map.Map Identifier WeakTerm
  , constraintEnv   :: [PreConstraint] -- for type inference
  , constraintQueue :: ConstraintQueue -- for (dependent) type inference
  , substEnv        :: SubstWeakTerm -- for (dependent) type inference
  , currentDir      :: FilePath
  , termEnv         :: [(Identifier, ([Identifier], Term))] -- f ~> (lam (x1 ... xn) e)
  , polEnv          :: [(Identifier, ([Identifier], Neg))] -- f ~> thunk (lam (x1 ... xn) e)
  , llvmEnv         :: [(Identifier, ([Identifier], LLVM))]
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
    , termEnv = []
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

newNameOfType :: WeakTerm -> WithEnv Identifier
newNameOfType t = do
  i <- newName
  insTypeEnv i t
  return i

lookupTypeEnv' :: String -> WithEnv WeakTerm
lookupTypeEnv' s = do
  mt <- gets (Map.lookup s . typeEnv)
  case mt of
    Nothing -> lift $ throwE $ s ++ " is not found in the type environment."
    Just t  -> return t

lookupNameEnv :: String -> WithEnv String
lookupNameEnv s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> lift $ throwE $ "undefined variable: " ++ show s

lookupNameEnvMaybe :: String -> WithEnv (Maybe String)
lookupNameEnvMaybe s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return $ Just s'
    Nothing -> return Nothing

insTypeEnv :: Identifier -> WeakTerm -> WithEnv ()
insTypeEnv i t = modify (\e -> e {typeEnv = Map.insert i t (typeEnv e)})

insTermEnv :: Identifier -> [Identifier] -> Term -> WithEnv ()
insTermEnv name args e =
  modify (\env -> env {termEnv = (name, (args, e)) : termEnv env})

insPolEnv :: Identifier -> [Identifier] -> Neg -> WithEnv ()
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

insConstraintEnv :: WeakTerm -> WeakTerm -> WithEnv ()
insConstraintEnv t1 t2 =
  modify (\e -> e {constraintEnv = (t1, t2) : constraintEnv e})

wrap :: f (Cofree f WeakMeta) -> WithEnv (Cofree f WeakMeta)
wrap a = do
  meta <- emptyMeta
  return $ meta :< a

newHole :: WithEnv WeakTerm
newHole = do
  h <- newNameWith "hole"
  m <- emptyMeta
  return $ m :< WeakTermHole h

newHoleOfType :: WeakTerm -> WithEnv WeakTerm
newHoleOfType t = do
  h <- newNameWith "hole"
  m <- metaOfType t
  return $ m :< WeakTermHole h

emptyMeta :: WithEnv WeakMeta
emptyMeta = do
  i <- newNameWith "hole"
  t <- liftIO $ newIORef (Left i)
  return $ WeakMeta {weakMetaType = Ref t, weakMetaLocation = Nothing}

metaOfType :: WeakTerm -> WithEnv WeakMeta
metaOfType t = do
  t' <- liftIO $ newIORef (Right t)
  return $ WeakMeta {weakMetaType = Ref t', weakMetaLocation = Nothing}

toWeakMeta :: TreeMeta -> WithEnv WeakMeta
toWeakMeta m = do
  i <- newNameWith "hole"
  t <- liftIO $ newIORef (Left i)
  return $
    WeakMeta {weakMetaType = Ref t, weakMetaLocation = treeMetaLocation m}
