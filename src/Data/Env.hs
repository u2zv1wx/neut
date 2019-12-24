{-# LANGUAGE FlexibleInstances #-}

module Data.Env where

import Control.Monad.Except
import Control.Monad.State
import Data.List (elemIndex)
import Data.Maybe (fromMaybe)
import System.Info

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
    , target :: Maybe Target
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
    , target = Nothing
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

lookupSubstEnv :: Identifier -> WithEnv (Maybe WeakTermPlus)
lookupSubstEnv i = do
  senv <- gets substEnv
  return $ lookup i senv

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
  i <- newNameWith "meta"
  return $ WeakMetaNonTerminal (Left i) Nothing

newMetaTerminal :: WeakMeta
newMetaTerminal = WeakMetaTerminal Nothing

newMetaOfType :: WeakTermPlus -> WithEnv WeakMeta
newMetaOfType t = do
  return $ WeakMetaNonTerminal (Right t) Nothing

toWeakMeta :: TreeMeta -> WithEnv WeakMeta
toWeakMeta m = do
  i <- newNameWith "meta"
  return $ WeakMetaNonTerminal (Left i) (treeMetaLocation m)

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Right (x, t)) = return (x, t)
supplyName (Left t) = do
  x <- newNameWith "hole"
  return (x, t)

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

-- distinguish [(x1, t1), ..., (xn, tn)] eは、は、eにおけるxiの出現をすべて新しい名前で置き換え、そうして得られたtermをe'として、
-- ([(x1, t1, {list-of-new-names-for-x1}), ..., (xm, tm, {list-of-new-names-for-xm})], e')を返す。
distinguish ::
     [(Identifier, CodePlus)]
  -> CodePlus
  -> WithEnv ([(Identifier, CodePlus, [Identifier])], CodePlus)
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
distinguishTheta z (ThetaSysCall num ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData z) ds
  return (concat vss, ThetaSysCall num ds')

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WithEnv WeakTermPlus
substWeakTermPlus sub (m, WeakTermTau) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermTau)
substWeakTermPlus sub (m, WeakTermTheta t) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermTheta t)
substWeakTermPlus sub (m, WeakTermUpsilon x) = do
  m' <- substWeakMeta sub m
  return $ fromMaybe (m', WeakTermUpsilon x) (lookup x sub)
substWeakTermPlus sub (m, WeakTermPi xts t) = do
  m' <- substWeakMeta sub m
  (xts', t') <- substWeakTermPlusBindingsWithBody sub xts t
  return (m', WeakTermPi xts' t')
substWeakTermPlus sub (m, WeakTermPiIntro xts body) = do
  m' <- substWeakMeta sub m
  (xts', body') <- substWeakTermPlusBindingsWithBody sub xts body
  return (m', WeakTermPiIntro xts' body')
substWeakTermPlus sub (m, WeakTermPiElim e es) = do
  m' <- substWeakMeta sub m
  e' <- substWeakTermPlus sub e
  es' <- mapM (substWeakTermPlus sub) es
  return (m', WeakTermPiElim e' es')
substWeakTermPlus sub (m, WeakTermMu (x, t) e) = do
  m' <- substWeakMeta sub m
  t' <- substWeakTermPlus sub t
  e' <- substWeakTermPlus (filter (\(k, _) -> k /= x) sub) e
  return (m', WeakTermMu (x, t') e')
substWeakTermPlus sub (m, WeakTermZeta s) = do
  m' <- substWeakMeta sub m
  return $ fromMaybe (m', WeakTermZeta s) (lookup s sub)
substWeakTermPlus sub (m, WeakTermIntS size x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermIntS size x)
substWeakTermPlus sub (m, WeakTermIntU size x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermIntU size x)
substWeakTermPlus sub (m, WeakTermInt x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermInt x)
substWeakTermPlus sub (m, WeakTermFloat16 x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat16 x)
substWeakTermPlus sub (m, WeakTermFloat32 x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat32 x)
substWeakTermPlus sub (m, WeakTermFloat64 x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat64 x)
substWeakTermPlus sub (m, WeakTermFloat x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat x)
substWeakTermPlus sub (m, WeakTermEnum x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermEnum x)
substWeakTermPlus sub (m, WeakTermEnumIntro l) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermEnumIntro l)
substWeakTermPlus sub (m, WeakTermEnumElim e branchList) = do
  m' <- substWeakMeta sub m
  e' <- substWeakTermPlus sub e
  let (caseList, es) = unzip branchList
  es' <- mapM (substWeakTermPlus sub) es
  return (m', WeakTermEnumElim e' (zip caseList es'))
substWeakTermPlus sub (m, WeakTermArray kind from to) = do
  m' <- substWeakMeta sub m
  from' <- substWeakTermPlus sub from
  to' <- substWeakTermPlus sub to
  return (m', WeakTermArray kind from' to')
substWeakTermPlus sub (m, WeakTermArrayIntro kind les) = do
  m' <- substWeakMeta sub m
  let (ls, es) = unzip les
  es' <- mapM (substWeakTermPlus sub) es
  return (m', WeakTermArrayIntro kind (zip ls es'))
substWeakTermPlus sub (m, WeakTermArrayElim kind e1 e2) = do
  m' <- substWeakMeta sub m
  e1' <- substWeakTermPlus sub e1
  e2' <- substWeakTermPlus sub e2
  return (m', WeakTermArrayElim kind e1' e2')

substWeakTermPlusBindingsWithBody ::
     SubstWeakTerm
  -> [(Identifier, WeakTermPlus)]
  -> WeakTermPlus
  -> WithEnv ([(Identifier, WeakTermPlus)], WeakTermPlus)
substWeakTermPlusBindingsWithBody sub [] e = do
  e' <- substWeakTermPlus sub e
  return ([], e')
substWeakTermPlusBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  (xts', e') <- substWeakTermPlusBindingsWithBody sub' xts e
  t' <- substWeakTermPlus sub t
  return ((x, t') : xts', e')

substWeakMeta :: SubstWeakTerm -> WeakMeta -> WithEnv WeakMeta
substWeakMeta _ m@(WeakMetaTerminal _) = return m
substWeakMeta sub (WeakMetaNonTerminal (Right t) ml) = do
  t' <- substWeakTermPlus sub t
  return $ WeakMetaNonTerminal (Right t') ml
substWeakMeta sub (WeakMetaNonTerminal (Left i) ml) = do
  senv <- gets substEnv
  case lookup i senv of
    Nothing -> throwError "substWeakMeta for Nothing"
    Just t -> do
      t' <- substWeakTermPlus sub t
      return $ WeakMetaNonTerminal (Right t') ml

compose :: SubstWeakTerm -> SubstWeakTerm -> WithEnv SubstWeakTerm
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  liftIO $ putStrLn $ "before subst. len =" ++ show (length codS2)
  codS2' <- mapM (substWeakTermPlus s1) codS2
  liftIO $ putStrLn "after subst"
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  return $ fromS1 ++ zip domS2 codS2'
