{-# LANGUAGE FlexibleInstances #-}

module Data.Env where

import Control.Monad.State
import Control.Monad.Trans.Except
import Data.IORef
import Data.List (elemIndex)

import Data.Basic
import Data.Code
import Data.Constraint
import Data.LLVM
import Data.Tree
import Data.WeakTerm

import qualified Data.Map.Strict as Map

import qualified Data.PQueue.Min as Q

type ConstraintQueue = Q.MinQueue EnrichedConstraint

data Env =
  Env
    { count :: Int -- to generate fresh symbols
    , currentDir :: FilePath
    , keywordEnv :: [Identifier] -- list of reserved keywords
    , notationEnv :: [(TreePlus, TreePlus)] -- macro transformers
    , constantEnv :: [Identifier]
    , epsilonEnv :: [(Identifier, [Identifier])] -- [("choice", ["left", "right"]), ...]
    , nameEnv :: [(Identifier, Identifier)] -- [("foo", "foo.13"), ...]
    , typeEnv :: Map.Map Identifier WeakTermPlus -- var ~> typeof(var)
    , constraintEnv :: [PreConstraint] -- for type inference
    , constraintQueue :: ConstraintQueue -- for (dependent) type inference
    , substEnv :: SubstWeakTerm -- metavar ~> beta-equivalent weakterm
    , codeEnv :: [(Identifier, ([Identifier], CodePlus))] -- f ~> thunk (lam (x1 ... xn) e)
    , llvmEnv :: [(Identifier, ([Identifier], LLVM))]
    }

initialEnv :: FilePath -> Env
initialEnv path =
  Env
    { count = 0
    , notationEnv = []
    , keywordEnv = []
    , constantEnv = []
    , epsilonEnv = []
    , nameEnv = []
    , typeEnv = Map.empty
    , codeEnv = []
    , llvmEnv = []
    , constraintEnv = []
    , constraintQueue = Q.empty
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

lookupTypeEnv :: String -> WithEnv WeakTermPlus
lookupTypeEnv s = do
  mt <- lookupTypeEnvMaybe s
  case mt of
    Just t -> return t
    Nothing -> lift $ throwE $ s ++ " is not found in the type environment."

lookupTypeEnvMaybe :: String -> WithEnv (Maybe WeakTermPlus)
lookupTypeEnvMaybe s = do
  mt <- gets (Map.lookup s . typeEnv)
  case mt of
    Nothing -> return Nothing
    Just t -> return $ Just t

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

insCodeEnv :: Identifier -> [Identifier] -> CodePlus -> WithEnv ()
insCodeEnv name args e =
  modify (\env -> env {codeEnv = (name, (args, e)) : codeEnv env})

insLLVMEnv :: Identifier -> [Identifier] -> LLVM -> WithEnv ()
insLLVMEnv funName args e =
  modify (\env -> env {llvmEnv = (funName, (args, e)) : llvmEnv env})

insEpsilonEnv :: Identifier -> [Identifier] -> WithEnv ()
insEpsilonEnv name epsilonList =
  modify (\e -> e {epsilonEnv = (name, epsilonList) : epsilonEnv e})

lookupKind :: Identifier -> WithEnv Identifier
lookupKind name = do
  env <- get
  lookupKind' name $ epsilonEnv env

lookupKind' :: Identifier -> [(Identifier, [Identifier])] -> WithEnv Identifier
lookupKind' i [] = lift $ throwE $ "no such epsilon-intro is defined: " ++ i
lookupKind' i ((j, ls):xs) =
  if i `elem` ls
    then return j
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
    Just i -> Just i

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

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Right (x, t)) = return (x, t)
supplyName (Left t) = do
  x <- newNameWith "hole"
  return (x, t)

discernData :: Identifier -> DataPlus -> WithEnv ([Identifier], DataPlus)
discernData z d@(ml, DataUpsilon x) =
  if x /= z
    then return ([], d)
    else do
      x' <- newNameWith z
      return ([x'], (ml, DataUpsilon x'))
discernData z (ml, DataSigmaIntro ds) = do
  (vss, ds') <- unzip <$> mapM (discernData z) ds
  return (concat vss, (ml, DataSigmaIntro ds'))
discernData _ d = return ([], d)

-- FIXME: これのEpsilonElimのところの取り扱いがおかしい気がする。
-- freeすべきかどうかはbranchによって変わるはず。
discernCode :: Identifier -> CodePlus -> WithEnv ([Identifier], CodePlus)
discernCode z (ml, CodeTheta theta) = do
  (vs, theta') <- discernTheta z theta
  return (vs, (ml, CodeTheta theta'))
discernCode z (ml, CodeEpsilonElim (x, lowType) d branchList) = do
  (vs, d') <- discernData z d
  if x == z
    then return (vs, (ml, CodeEpsilonElim (x, lowType) d' branchList))
    else do
      let (cs, es) = unzip branchList
      (vss, es') <- unzip <$> mapM (discernCode z) es
      return
        (vs ++ concat vss, (ml, CodeEpsilonElim (x, lowType) d' (zip cs es')))
discernCode z (ml, CodePiElimDownElim d ds) = do
  (vs, d') <- discernData z d
  (vss, ds') <- unzip <$> mapM (discernData z) ds
  return (vs ++ concat vss, (ml, CodePiElimDownElim d' ds'))
discernCode z (ml, CodeSigmaElim xs d e) = do
  (vs1, d') <- discernData z d
  if z `elem` xs
    then return (vs1, (ml, CodeSigmaElim vs1 d' e))
    else do
      (vs2, e') <- discernCode z e
      return (vs1 ++ vs2, (ml, CodeSigmaElim vs1 d' e'))
discernCode z (ml, CodeUpIntro d) = do
  (vs, d') <- discernData z d
  return (vs, (ml, CodeUpIntro d'))
discernCode z (ml, CodeUpElim x e1 e2) = do
  (vs1, e1') <- discernCode z e1
  if x == z
    then return (vs1, (ml, CodeUpElim x e1' e2))
    else do
      (vs2, e2') <- discernCode z e2
      return (vs1 ++ vs2, (ml, CodeUpElim x e1' e2'))

discernTheta :: Identifier -> Theta -> WithEnv ([Identifier], Theta)
discernTheta z (ThetaArith arith lowType d1 d2) = do
  (vs1, d1') <- discernData z d1
  (vs2, d2') <- discernData z d2
  return (vs1 ++ vs2, ThetaArith arith lowType d1' d2')
discernTheta z (ThetaPrint d) = do
  (vs, d') <- discernData z d
  return (vs, ThetaPrint d')
