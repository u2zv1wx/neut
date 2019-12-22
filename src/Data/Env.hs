{-# LANGUAGE FlexibleInstances #-}

module Data.Env where

import Control.Monad.Except
import Control.Monad.State
import Data.IORef
import Data.List (elemIndex)

import Data.Basic
import Data.Code
import Data.Constraint
import Data.LLVM
import Data.Term
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
    , enumEnv :: [(Identifier, [Identifier])] -- [("choice", ["left", "right"]), ...]
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
    , enumEnv = []
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
    Nothing -> throwError $ s ++ " is not found in the type environment."

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
    Nothing -> throwError $ "undefined variable: " ++ show s

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
  env <- get
  lookupEnumSet' name $ enumEnv env

lookupEnumSet' ::
     Identifier -> [(Identifier, [Identifier])] -> WithEnv [Identifier]
lookupEnumSet' name [] = throwError $ "no such enum defined: " ++ show name
lookupEnumSet' name ((_, ls):xs) =
  if name `elem` ls
    then return ls
    else lookupEnumSet' name xs

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

-- distinguish [(x1, t1), ..., (xn, tn)] eは、は、eにおけるxiの出現をすべて新しい名前で置き換え、そうして得られたtermをe'として、
-- ([(x1, t1, {list-of-new-names-for-x1}), ..., (xm, tm, {list-of-new-names-for-xm})], e')を返す。
distinguish ::
     [(Identifier, TermPlus)]
  -> CodePlus
  -> WithEnv ([(Identifier, TermPlus, [Identifier])], CodePlus)
distinguish [] e = return ([], e)
distinguish ((x, t):xts) e = do
  (xtzss, e') <- distinguish xts e
  (xs, e'') <- distinguishCode x e'
  return ((x, t, xs) : xtzss, e'')

distinguishData :: Identifier -> DataPlus -> WithEnv ([Identifier], DataPlus)
distinguishData z d@(ml, DataUpsilon x) =
  if x /= z
    then return ([], d)
    else do
      x' <- newNameWith z
      return ([x'], (ml, DataUpsilon x'))
distinguishData z (ml, DataSigmaIntro ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData z) ds
  return (concat vss, (ml, DataSigmaIntro ds'))
distinguishData _ d = return ([], d)

distinguishCode :: Identifier -> CodePlus -> WithEnv ([Identifier], CodePlus)
distinguishCode z (ml, CodeTheta theta) = do
  (vs, theta') <- distinguishTheta z theta
  return (vs, (ml, CodeTheta theta'))
distinguishCode z (ml, CodePiElimDownElim d ds) = do
  (vs, d') <- distinguishData z d
  (vss, ds') <- unzip <$> mapM (distinguishData z) ds
  return (vs ++ concat vss, (ml, CodePiElimDownElim d' ds'))
distinguishCode z (ml, CodeSigmaElim xs d e) = do
  (vs1, d') <- distinguishData z d
  if z `elem` xs
    then return (vs1, (ml, CodeSigmaElim vs1 d' e))
    else do
      (vs2, e') <- distinguishCode z e
      return (vs1 ++ vs2, (ml, CodeSigmaElim vs1 d' e'))
distinguishCode z (ml, CodeUpIntro d) = do
  (vs, d') <- distinguishData z d
  return (vs, (ml, CodeUpIntro d'))
distinguishCode z (ml, CodeUpElim x e1 e2) = do
  (vs1, e1') <- distinguishCode z e1
  if x == z
    then return (vs1, (ml, CodeUpElim x e1' e2))
    else do
      (vs2, e2') <- distinguishCode z e2
      return (vs1 ++ vs2, (ml, CodeUpElim x e1' e2'))
distinguishCode z (ml, CodeEnumElim d branchList) = do
  (vs, d') <- distinguishData z d
  let (cs, es) = unzip branchList
  (vss, es') <- unzip <$> mapM (distinguishCode z) es
  return (vs ++ concat vss, (ml, CodeEnumElim d' (zip cs es')))
distinguishCode z (ml, CodeArrayElim k d1 d2) = do
  (vs1, d1') <- distinguishData z d1
  (vs2, d2') <- distinguishData z d2
  return (vs1 ++ vs2, (ml, CodeArrayElim k d1' d2'))

distinguishTheta :: Identifier -> Theta -> WithEnv ([Identifier], Theta)
distinguishTheta z (ThetaUnaryOp op lowType d) = do
  (vs, d') <- distinguishData z d
  return (vs, ThetaUnaryOp op lowType d')
distinguishTheta z (ThetaBinaryOp op lowType d1 d2) = do
  (vs1, d1') <- distinguishData z d1
  (vs2, d2') <- distinguishData z d2
  return (vs1 ++ vs2, ThetaBinaryOp op lowType d1' d2')
distinguishTheta z (ThetaPrint d) = do
  (vs, d') <- distinguishData z d
  return (vs, ThetaPrint d')
