{-# LANGUAGE OverloadedStrings #-}

module Data.Env where

import Control.Monad.Except
import Control.Monad.State
import Data.List (find)
import Path
import Path.IO
import System.Info

import Data.Basic
import Data.Code
import Data.Constraint
import Data.LLVM
import Data.Log
import Data.Term
import Data.Tree
import Data.WeakTerm

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import qualified Text.Show.Pretty as Pr

type ConstraintQueue = Q.MinQueue EnrichedConstraint

data VisitInfo
  = VisitInfoActive
  | VisitInfoFinish

type FileEnv = Map.HashMap (Path Abs File) VisitInfo

type RuleEnv = Map.HashMap Int (Maybe [Data.WeakTerm.IdentifierPlus])

type UnivInstEnv = IntMap.IntMap (S.Set Int)

type TypeEnv = IntMap.IntMap (TermPlus, UnivLevelPlus)

data Env =
  Env
    { count :: Int
    , ppCount :: Int -- count used only for pretty printing
    -- parse
    , inputText :: T.Text
    , inputLine :: Int
    , inputColumn :: Int
    , phase :: Int
    , target :: Maybe Target
    , keywordEnv :: S.Set T.Text -- list of reserved keywords
    , notationEnv :: [(TreePlus, TreePlus)] -- macro transformers
    , constantEnv :: Map.HashMap T.Text Int
    , fileEnv :: FileEnv -- path ~> identifiers defined in the file at toplevel
    , traceEnv :: [Path Abs File]
    , enumEnv :: Map.HashMap T.Text [(T.Text, Int)] -- [("choice", [("left", 0), ("right", 1)]), ...]
    , revEnumEnv :: Map.HashMap T.Text (T.Text, Int) -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
    , llvmEnumEnv :: Map.HashMap T.Text T.Text -- "list:nil" ~> "list-nil-12", etc.
    , revCaseEnv :: IntMap.IntMap T.Text
    , indEnumEnv :: Map.HashMap T.Text [(T.Text, Int)] -- [("nat", [("zero", 0), ("succ", 1)]), ...]
    , nameEnv :: Map.HashMap T.Text T.Text
    , revNameEnv :: IntMap.IntMap Int -- [("foo.13", "foo"), ...] (as corresponding int)
    , prefixEnv :: [T.Text]
    , namespace :: [T.Text]
    , formationEnv :: IntMap.IntMap (Maybe WeakTermPlus)
    , labelEnv :: Map.HashMap T.Text [T.Text] -- "stream" ~> ["stream", "other-record-type", "head", "tail", "other-destructor"]
    , inductiveEnv :: RuleEnv -- "list" ~> (cons, Pi (A : tau). A -> list A -> list A)
    , coinductiveEnv :: RuleEnv -- "tail" ~> (head, Pi (A : tau). stream A -> A)
    , introEnv :: S.Set Int -- set of the names of constructors (e.g. ["nil", "cons", "zero", "succ", ...] (as int))
    , nonCandSet :: S.Set T.Text
    -- elaborate
    , impEnv :: IntMap.IntMap [Int] -- var ~> (index of implicit arguments of the var)
    , weakTypeEnv :: IntMap.IntMap (WeakTermPlus, UnivLevelPlus) -- var ~> (typeof(var), level-of-type)
    , equalityEnv :: [(UnivLevel, UnivLevel)]
    , univInstEnv :: UnivInstEnv
    , univRenameEnv :: IntMap.IntMap Int
    , typeEnv :: TypeEnv
    , constraintEnv :: [PreConstraint] -- for type inference
    , constraintQueue :: ConstraintQueue
    , levelEnv :: [LevelConstraint]
    , substEnv :: IntMap.IntMap WeakTermPlus -- metavar ~> beta-equivalent weakterm
    , zetaEnv :: IntMap.IntMap (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
    , patVarEnv :: S.Set Int
    -- clarify
    , cacheEnv :: IntMap.IntMap (Either TermPlus CodePlus)
    , codeEnv :: Map.HashMap T.Text Definition -- f ~> thunk (lam (x1 ... xn) e)
    , nameSet :: S.Set T.Text
    -- LLVM
    , llvmEnv :: Map.HashMap T.Text ([Identifier], LLVM)
    , declEnv :: Map.HashMap T.Text ([LowType], LowType) -- external functions that must be declared in LLVM IR
    , nopFreeSet :: S.Set Int
    }

initialEnv :: Env
initialEnv =
  Env
    { count = 0
    , ppCount = 0
    , inputText = T.empty
    , inputLine = 0
    , inputColumn = 0
    , phase = 0
    , target = Nothing
    , notationEnv = []
    , keywordEnv = S.empty
    , constantEnv = Map.empty
    , enumEnv = Map.empty
    , indEnumEnv = Map.empty
    , fileEnv = Map.empty
    , traceEnv = []
    , revEnumEnv = Map.empty
    , llvmEnumEnv = Map.empty
    , revCaseEnv = IntMap.empty
    , nameEnv = Map.empty
    , revNameEnv = IntMap.empty
    , prefixEnv = []
    , namespace = []
    , formationEnv = IntMap.empty
    , inductiveEnv = Map.empty
    , coinductiveEnv = Map.empty
    , introEnv = S.empty
    , nonCandSet = S.empty
    , labelEnv = Map.empty
    , equalityEnv = []
    , univInstEnv = IntMap.empty
    , univRenameEnv = IntMap.empty
    , impEnv = IntMap.empty
    , weakTypeEnv = IntMap.empty
    , typeEnv = IntMap.empty
    , cacheEnv = IntMap.empty
    , codeEnv = Map.empty
    , llvmEnv = Map.empty
    , declEnv =
        Map.fromList
          [ ("malloc", ([LowTypeIntS 64], LowTypeVoidPtr))
          , ("free", ([LowTypeVoidPtr], LowTypeVoid))
          ]
    , constraintEnv = []
    , constraintQueue = Q.empty
    , levelEnv = []
    , substEnv = IntMap.empty
    , zetaEnv = IntMap.empty
    , patVarEnv = S.empty
    , nameSet = S.empty
    , nopFreeSet = S.empty
    }

type WithEnv a = StateT Env (ExceptT [Log] IO) a

evalWithEnv :: WithEnv a -> Env -> IO (Either [Log] a)
evalWithEnv c env = do
  resultOrErr <- runExceptT (runStateT c env)
  case resultOrErr of
    Left err -> return $ Left err
    Right (result, _) -> return $ Right result

newCount :: WithEnv Int
newCount = do
  i <- gets count
  modify (\e -> e {count = i + 1})
  if i + 1 == 0
    then raiseCritical' "counter exhausted"
    else return i

newCountPP :: WithEnv Int
newCountPP = do
  i <- gets ppCount
  modify (\e -> e {ppCount = i + 1})
  if i + 1 == 0
    then raiseCritical' "counter exhausted"
    else return i

newNameWith :: Identifier -> WithEnv Identifier
newNameWith (I (s, _)) = do
  j <- newCount
  return $ I (s, j)

newNameWith' :: T.Text -> WithEnv Identifier
newNameWith' s = do
  i <- newCount
  return $ I (s, i)

newNameWith'' :: T.Text -> WithEnv Identifier
newNameWith'' s = do
  i <- newCount
  return $ I (s <> "-" <> T.pack (show i), i)

newHole :: Meta -> WithEnv WeakTermPlus
newHole m = do
  h <- newNameWith'' "hole"
  return (m, WeakTermZeta h)

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
    s -> raiseCritical' $ "unsupported target os: " <> T.pack (show s)

getArch :: WithEnv Arch
getArch = do
  case arch of
    "x86_64" -> return Arch64
    s -> raiseCritical' $ "unsupported target arch: " <> T.pack (show s)

newDataUpsilonWith :: Meta -> T.Text -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith m name = do
  x <- newNameWith' name
  return (x, (m, DataUpsilon x))

piUnivLevelsfrom :: [(a, b, (Meta, c))] -> (Meta, c) -> WithEnv [UnivLevelPlus]
piUnivLevelsfrom xts t = do
  let ms = map fst $ map (\(_, _, z) -> z) xts ++ [t]
  ls <- mapM (const newCount) ms
  return $ map UnivLevelPlus $ zip ms ls

insTypeEnv :: Identifier -> TermPlus -> UnivLevelPlus -> WithEnv ()
insTypeEnv (I (_, i)) t ml =
  modify (\e -> e {typeEnv = IntMap.insert i (t, ml) (typeEnv e)})

insTypeEnv' :: Data.Term.IdentifierPlus -> WithEnv ()
insTypeEnv' (_, I (_, i), t) = do
  l <- newCount
  let ml = UnivLevelPlus (fst t, l)
  modify (\e -> e {typeEnv = IntMap.insert i (t, ml) (typeEnv e)})

insTypeEnv'' :: Identifier -> TermPlus -> TypeEnv -> TypeEnv
insTypeEnv'' (I (_, i)) t tenv = do
  let ml = UnivLevelPlus (fst t, 0)
  IntMap.insert i (t, ml) tenv

lookupTypeEnv :: Identifier -> WithEnv (Maybe (TermPlus, UnivLevelPlus))
lookupTypeEnv (I (_, i)) = do
  tenv <- gets typeEnv
  return $ IntMap.lookup i tenv

lookupTypeEnv1 :: Meta -> Identifier -> WithEnv (TermPlus, UnivLevelPlus)
lookupTypeEnv1 m x@(I (_, i)) = do
  tenv <- gets typeEnv
  case IntMap.lookup i tenv of
    Just (t, l) -> return (t, l)
    Nothing ->
      raiseCritical m $ asText' x <> " is not found in the type environment."

lookupTypeEnv' :: Meta -> Identifier -> WithEnv TermPlus
lookupTypeEnv' m x = do
  tenv <- gets typeEnv
  lookupTypeEnv'' m x tenv

lookupTypeEnv'' :: Meta -> Identifier -> TypeEnv -> WithEnv TermPlus
lookupTypeEnv'' m x@(I (s, i)) tenv
  | Just _ <- asLowTypeMaybe s = do
    l <- newCount
    return (m, TermTau l)
  | Just op <- asUnaryOpMaybe s = unaryOpToType m op
  | Just op <- asBinaryOpMaybe s = binaryOpToType m op
  | Just lowType <- asArrayAccessMaybe s = arrayAccessToType m lowType
  | otherwise = do
    case IntMap.lookup i tenv of
      Just (t, _) -> return t
      Nothing ->
        raiseCritical m $ asText' x <> " is not found in the type environment."

lowTypeToType :: Meta -> LowType -> WithEnv TermPlus
lowTypeToType m (LowTypeIntS s) = return (m, TermEnum (EnumTypeIntS s))
lowTypeToType m (LowTypeIntU s) = return (m, TermEnum (EnumTypeIntU s))
lowTypeToType m (LowTypeFloat s) = do
  let x = "f" <> T.pack (show (sizeAsInt s))
  i <- lookupConstNum x
  return (m, TermConst (I (x, i)) emptyUP)
lowTypeToType m _ = raiseCritical m "invalid argument passed to lowTypeToType"

unaryOpToType :: Meta -> UnaryOp -> WithEnv TermPlus
unaryOpToType m op = do
  let (dom, cod) = unaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x <- newNameWith' "arg"
  let xts = [(m, x, dom')]
  mls <- piUnivLevelsfrom xts cod'
  return (m, TermPi mls xts cod')

binaryOpToType :: Meta -> BinaryOp -> WithEnv TermPlus
binaryOpToType m op = do
  let (dom, cod) = binaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x1 <- newNameWith' "arg"
  x2 <- newNameWith' "arg"
  let xts = [(m, x1, dom'), (m, x2, dom')]
  mls <- piUnivLevelsfrom xts cod'
  return (m, TermPi mls xts cod')

arrayAccessToType :: Meta -> LowType -> WithEnv TermPlus
arrayAccessToType m lowType = do
  t <- lowTypeToType m lowType
  k <- lowTypeToArrayKind m lowType
  x1 <- newNameWith' "arg"
  x2 <- newNameWith' "arg"
  x3 <- newNameWith' "arg"
  let u64 = (m, TermEnum (EnumTypeIntU 64))
  let idx = (m, TermUpsilon x2)
  let arr = (m, TermArray idx k)
  let xts = [(m, x1, u64), (m, x2, u64), (m, x3, arr)]
  x4 <- newNameWith' "arg"
  x5 <- newNameWith' "arg"
  let cod = (m, TermSigma [(m, x4, arr), (m, x5, t)])
  mls <- piUnivLevelsfrom xts cod
  return (m, TermPi mls xts cod)

insEnumEnv :: Meta -> T.Text -> [(T.Text, Int)] -> WithEnv ()
insEnumEnv m name xis = do
  eenv <- gets enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat (Map.elems eenv))
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x -> raiseError m $ "the constant `" <> x <> "` is already defined"
    _ -> do
      let (xs, is) = unzip xis
      forM_ xs insLLVMEnumEnv
      let rev = Map.fromList $ zip xs (zip (repeat name) is)
      modify
        (\e ->
           e
             { enumEnv = Map.insert name xis (enumEnv e)
             , revEnumEnv = rev `Map.union` (revEnumEnv e)
             })

insLLVMEnumEnv :: T.Text -> WithEnv ()
insLLVMEnumEnv labelName = do
  j <- newCount
  let name = "_" <> T.pack (show j)
  lenv <- gets llvmEnumEnv
  modify (\env -> env {llvmEnumEnv = Map.insert labelName name lenv})

lookupLLVMEnumEnv :: Meta -> T.Text -> WithEnv T.Text
lookupLLVMEnumEnv m labelName = do
  lenv <- gets llvmEnumEnv
  case Map.lookup labelName lenv of
    Nothing -> raiseCritical m $ "no such enum-label defined: " <> labelName
    Just labelName' -> return labelName'

lookupConstNum :: T.Text -> WithEnv Int
lookupConstNum constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return i
    Nothing -> do
      i <- newCount
      modify (\env -> env {constantEnv = Map.insert constName i cenv})
      return i

lookupConstNum' :: Meta -> T.Text -> WithEnv Int
lookupConstNum' m constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return i
    Nothing -> raiseCritical m $ "no such constant: " <> constName

lookupConstantMaybe :: Meta -> [T.Text] -> T.Text -> WithEnv (Maybe Identifier)
lookupConstantMaybe m penv constName = do
  me <- lookupConstantMaybe'' constName
  case me of
    Just e -> return $ Just e
    Nothing -> lookupConstantMaybe' m penv constName

lookupConstantMaybe' :: Meta -> [T.Text] -> T.Text -> WithEnv (Maybe Identifier)
lookupConstantMaybe' _ [] _ = return Nothing
lookupConstantMaybe' m (prefix:prefixList) name = do
  me <- lookupConstantMaybe'' $ prefix <> ":" <> name
  case me of
    Just e -> return $ Just e
    Nothing -> lookupConstantMaybe' m prefixList name

lookupConstantMaybe'' :: T.Text -> WithEnv (Maybe Identifier)
lookupConstantMaybe'' constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return $ Just $ I (constName, i)
    Nothing
      | isConstant constName -> Just <$> lookupConstantPlus' constName
      | otherwise -> return Nothing

lookupConstantPlus :: Meta -> T.Text -> WithEnv WeakTermPlus
lookupConstantPlus m constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return (m, WeakTermConst (I (constName, i)) emptyUP)
    Nothing -> do
      i <- newCount
      let ident = I (constName, i)
      modify (\env -> env {constantEnv = Map.insert constName i cenv})
      return (m, WeakTermConst ident emptyUP)

lookupConstantPlus' :: T.Text -> WithEnv Identifier
lookupConstantPlus' constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return $ I (constName, i)
    Nothing -> do
      i <- newCount
      let ident = I (constName, i)
      modify (\env -> env {constantEnv = Map.insert constName i cenv})
      return ident

-- f32とかi64.addとかは定数
isConstant :: T.Text -> Bool
isConstant name
  | name == "f16" = True
  | name == "f32" = True
  | name == "f64" = True
  | Just _ <- asUnaryOpMaybe name = True
  | Just _ <- asBinaryOpMaybe name = True
  | Just _ <- asArrayAccessMaybe name = True
  | otherwise = False

-- for debug
p :: String -> WithEnv ()
p s = liftIO $ putStrLn s

p' :: (Show a) => a -> WithEnv ()
p' s = liftIO $ putStrLn $ Pr.ppShow s

pp :: WeakTermPlus -> WithEnv ()
pp e = liftIO $ TIO.putStrLn $ toText e

toStr :: (Show a) => a -> String
toStr s = Pr.ppShow s

lowTypeToArrayKind :: Meta -> LowType -> WithEnv ArrayKind
lowTypeToArrayKind m lowType =
  case lowTypeToArrayKindMaybe lowType of
    Just k -> return k
    Nothing -> raiseCritical m "Infer.lowTypeToArrayKind"

raiseError :: Meta -> T.Text -> WithEnv a
raiseError m text = throwError [logError (getPosInfo m) text]

raiseCritical :: Meta -> T.Text -> WithEnv a
raiseCritical m text = throwError [logCritical (getPosInfo m) text]

raiseCritical' :: T.Text -> WithEnv a
raiseCritical' text = throwError [logCritical' text]

getCurrentFilePath :: WithEnv (Path Abs File)
getCurrentFilePath = do
  tenv <- gets traceEnv
  return $ head tenv

getCurrentDirPath :: WithEnv (Path Abs Dir)
getCurrentDirPath = parent <$> getCurrentFilePath

getLibraryDirPath :: WithEnv (Path Abs Dir)
getLibraryDirPath = do
  homeDirPath <- getHomeDir
  relLibPath <- parseRelDir ".local/share/neut/library"
  return $ homeDirPath </> relLibPath

note :: T.Text -> WithEnv ()
note str = liftIO $ outputLog True $ logInfo' str
