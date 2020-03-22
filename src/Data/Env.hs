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

data Env =
  Env
    { count :: Int
    -- parse
    , inputText :: T.Text
    , inputLine :: Int
    , inputColumn :: Int
    , phase :: Int
    , target :: Maybe Target
    , keywordEnv :: S.Set T.Text -- list of reserved keywords
    , defEnv :: S.Set T.Text -- list of defined variables
    , notationEnv :: [(TreePlus, TreePlus)] -- macro transformers
    , constantEnv :: Map.HashMap T.Text Int
    , fileEnv :: FileEnv -- path ~> identifiers defined in the file at toplevel
    , traceEnv :: [Path Abs File]
    , enumEnv :: Map.HashMap T.Text [(T.Text, Int)] -- [("choice", [("left", 0), ("right", 1)]), ...]
    , revEnumEnv :: Map.HashMap T.Text (T.Text, Int) -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
    , indEnumEnv :: Map.HashMap T.Text [(T.Text, Int)] -- [("nat", [("zero", 0), ("succ", 1)]), ...]
    , nameEnv :: Map.HashMap T.Text T.Text
    , revNameEnv :: IntMap.IntMap Int -- [("foo.13", "foo"), ...] (as corresponding int)
    -- , specifiedNameSet :: S.Set T.Text
    , formationEnv :: IntMap.IntMap (Maybe WeakTermPlus)
    , labelEnv :: Map.HashMap T.Text [T.Text] -- "stream" ~> ["stream", "other-record-type", "head", "tail", "other-destructor"]
    , inductiveEnv :: RuleEnv -- "list" ~> (cons, Pi (A : tau). A -> list A -> list A)
    , coinductiveEnv :: RuleEnv -- "tail" ~> (head, Pi (A : tau). stream A -> A)
    -- elaborate
    , impEnv :: IntMap.IntMap [Int] -- var ~> (index of implicit arguments of the var)
    , weakTypeEnv :: IntMap.IntMap (WeakTermPlus, UnivLevelPlus) -- var ~> (typeof(var), level-of-type)
    , equalityEnv :: [(UnivLevel, UnivLevel)]
    , univInstEnv :: UnivInstEnv
    , univRenameEnv :: IntMap.IntMap Int
    , typeEnv :: IntMap.IntMap (TermPlus, UnivLevelPlus)
    , constraintEnv :: [PreConstraint] -- for type inference
    , constraintQueue :: ConstraintQueue
    , levelEnv :: [LevelConstraint]
    , substEnv :: IntMap.IntMap WeakTermPlus -- metavar ~> beta-equivalent weakterm
    , zetaEnv :: IntMap.IntMap (WeakTermPlus, WeakTermPlus, UnivLevelPlus)
    , patVarEnv :: S.Set Int
    -- clarify
    , chainEnv :: IntMap.IntMap [(Meta, Identifier, TermPlus)] -- var/const ~> the closed var chain of its type
    , codeEnv :: Map.HashMap T.Text Definition -- f ~> thunk (lam (x1 ... xn) e)
    , nameSet :: S.Set T.Text
    -- LLVM
    , llvmEnv :: Map.HashMap T.Text ([Identifier], LLVM)
    , declEnv :: Map.HashMap T.Text ([LowType], LowType) -- external functions that must be declared in LLVM IR
    }

initialEnv :: Env
initialEnv =
  Env
    { count = 0
    , inputText = T.empty
    , inputLine = 0
    , inputColumn = 0
    , phase = 0
    , target = Nothing
    , notationEnv = []
    , keywordEnv = S.empty
    , defEnv = S.empty
    , constantEnv = Map.empty
    , enumEnv = Map.empty
    , indEnumEnv = Map.empty
    , fileEnv = Map.empty
    , traceEnv = []
    , revEnumEnv = Map.empty
    , nameEnv = Map.empty
    , revNameEnv = IntMap.empty
    -- , specifiedNameSet = S.empty
    , formationEnv = IntMap.empty
    , inductiveEnv = Map.empty
    , coinductiveEnv = Map.empty
    , labelEnv = Map.empty
    , equalityEnv = []
    , univInstEnv = IntMap.empty
    , univRenameEnv = IntMap.empty
    , impEnv = IntMap.empty
    , weakTypeEnv = IntMap.empty
    , typeEnv = IntMap.empty
    , chainEnv = IntMap.empty
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

llvmString :: T.Text -> T.Text
llvmString "" = error "llvmString called for the empty string"
llvmString s = T.cons (llvmHeadChar $ T.head s) (T.map llvmTailChar $ T.tail s)

llvmHeadCharSet :: S.Set Char
llvmHeadCharSet =
  S.fromList $
  "-$._" <> "abcdefghijklmnopqrstuvwxyz" <> "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

llvmHeadChar :: Char -> Char
llvmHeadChar x =
  if x `S.member` llvmHeadCharSet
    then x
    else '-'

llvmTailCharSet :: S.Set Char
llvmTailCharSet =
  S.fromList $
  "-$._" <>
  "abcdefghijklmnopqrstuvwxyz" <> "ABCDEFGHIJKLMNOPQRSTUVWXYZ" <> "0123456789"

llvmTailChar :: Char -> Char
llvmTailChar x =
  if x `S.member` llvmTailCharSet
    then x
    else '-'

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
    s -> raiseError' $ "unsupported target os: " <> T.pack (show s)

getArch :: WithEnv Arch
getArch = do
  case arch of
    "x86_64" -> return Arch64
    s -> raiseError' $ "unsupported target arch: " <> T.pack (show s)

newDataUpsilonWith :: T.Text -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith name = newDataUpsilonWith' name emptyMeta

newDataUpsilonWith' :: T.Text -> Meta -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith' name m = do
  x <- newNameWith' name
  return (x, (m, DataUpsilon x))

piUnivLevelsfrom ::
     [Data.WeakTerm.IdentifierPlus] -> WeakTermPlus -> WithEnv [UnivLevelPlus]
piUnivLevelsfrom xts t = do
  let ms = map fst $ map (\(_, _, z) -> z) xts ++ [t]
  ls <- mapM (const newCount) ms
  return $ map UnivLevelPlus $ zip ms ls

insTypeEnv :: Identifier -> TermPlus -> UnivLevelPlus -> WithEnv ()
insTypeEnv (I (_, i)) t ml =
  modify (\e -> e {typeEnv = IntMap.insert i (t, ml) (typeEnv e)})

insTypeEnv' :: Identifier -> TermPlus -> WithEnv ()
insTypeEnv' (I (_, i)) t = do
  l <- newCount
  let ml = UnivLevelPlus (fst t, l)
  modify (\e -> e {typeEnv = IntMap.insert i (t, ml) (typeEnv e)})

lookupTypeEnv :: Identifier -> WithEnv (Maybe (TermPlus, UnivLevelPlus))
lookupTypeEnv (I (_, i)) = do
  tenv <- gets typeEnv
  return $ IntMap.lookup i tenv

lookupTypeEnv' :: Identifier -> WithEnv TermPlus
lookupTypeEnv' (I (s, i))
  | Just _ <- asLowTypeMaybe s = do
    l <- newCount
    return (emptyMeta, TermTau l)
  | Just op <- asUnaryOpMaybe s = unaryOpToType emptyMeta op
  | Just op <- asBinaryOpMaybe s = binaryOpToType emptyMeta op
  | Just lowType <- asArrayAccessMaybe s = arrayAccessToType emptyMeta lowType
  | otherwise = do
    mt <- gets (IntMap.lookup i . typeEnv)
    case mt of
      Just (t, _) -> return t
      Nothing -> raiseCritical' $ s <> " is not found in the type environment."

lowTypeToType :: Meta -> LowType -> WithEnv TermPlus
lowTypeToType m (LowTypeIntS s) = return (m, TermEnum (EnumTypeIntS s))
lowTypeToType m (LowTypeIntU s) = return (m, TermEnum (EnumTypeIntU s))
lowTypeToType m (LowTypeFloat s) = do
  let x = "f" <> T.pack (show (sizeAsInt s))
  i <- lookupConstNum x
  return (m, TermConst (I (x, i)))
lowTypeToType _ _ = raiseCritical' "invalid argument passed to lowTypeToType"

unaryOpToType :: Meta -> UnaryOp -> WithEnv TermPlus
unaryOpToType m op = do
  let (dom, cod) = unaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x <- newNameWith' "arg"
  let xts = [(m, x, dom')]
  return (m, TermPi [] xts cod')

binaryOpToType :: Meta -> BinaryOp -> WithEnv TermPlus
binaryOpToType m op = do
  let (dom, cod) = binaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x1 <- newNameWith' "arg"
  x2 <- newNameWith' "arg"
  let xts = [(m, x1, dom'), (m, x2, dom')]
  return (m, TermPi [] xts cod')

arrayAccessToType :: Meta -> LowType -> WithEnv TermPlus
arrayAccessToType m lowType = do
  t <- lowTypeToType m lowType
  k <- lowTypeToArrayKind lowType
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
  return (m, TermPi [] xts cod)

insEnumEnv :: Meta -> T.Text -> [(T.Text, Int)] -> WithEnv ()
insEnumEnv m name xis = do
  eenv <- gets enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat (Map.elems eenv))
  -- let name' = llvmString name
  -- let (xs, is) = unzip xis
  -- let xs' = map llvmString xs
  -- let xis' = zip xs' is
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x -> raiseError m $ "the constant `" <> x <> "` is already defined"
    _ -> do
      let (xs, is) = unzip xis
      let rev = Map.fromList $ zip xs (zip (repeat name) is)
      modify
        (\e ->
           e
             { enumEnv = Map.insert name xis (enumEnv e)
             , revEnumEnv = rev `Map.union` (revEnumEnv e)
             })

lookupConstNum :: T.Text -> WithEnv Int
lookupConstNum constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return i
    Nothing -> do
      i <- newCount
      modify (\env -> env {constantEnv = Map.insert constName i cenv})
      return i

lookupConstNum' :: T.Text -> WithEnv Int
lookupConstNum' constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return i
    Nothing -> raiseCritical' $ "no such constant: " <> constName

lookupConstantMaybe :: Meta -> T.Text -> WithEnv (Maybe WeakTermPlus)
lookupConstantMaybe m constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return $ Just (m, WeakTermConst $ I (constName, i))
    Nothing
      | isConstant constName -> Just <$> lookupConstantPlus m constName
      | otherwise -> return Nothing

lookupConstantPlus :: Meta -> T.Text -> WithEnv WeakTermPlus
lookupConstantPlus m constName = do
  cenv <- gets constantEnv
  case Map.lookup constName cenv of
    Just i -> return (m, WeakTermConst $ I (constName, i))
    Nothing -> do
      i <- newCount
      let ident = I (constName, i)
      modify (\env -> env {constantEnv = Map.insert constName i cenv})
      return (m, WeakTermConst ident)

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

lowTypeToArrayKind :: LowType -> WithEnv ArrayKind
lowTypeToArrayKind lowType =
  case lowTypeToArrayKindMaybe lowType of
    Just k -> return k
    Nothing -> raiseCritical' "Infer.lowTypeToArrayKind"

raiseError :: Meta -> T.Text -> WithEnv a
raiseError m text = throwError [logError (getPosInfo m) text]

raiseError' :: T.Text -> WithEnv a
raiseError' text = throwError [logError' text]

raiseCritical :: Meta -> T.Text -> WithEnv a
raiseCritical m text = throwError [logCritical (getPosInfo m) text]

raiseCritical' :: T.Text -> WithEnv a
raiseCritical' text = throwError [logCritical' text]

isDefinedEnumValue :: T.Text -> WithEnv Bool
isDefinedEnumValue name = do
  env <- get
  let labelList = join $ Map.elems $ enumEnv env
  return $ name `elem` map fst labelList

isDefinedEnumType :: T.Text -> WithEnv Bool
isDefinedEnumType name = do
  env <- get
  let enumNameList = Map.keys $ enumEnv env
  return $ name `elem` enumNameList

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

outputNote :: T.Text -> WithEnv ()
outputNote str = do
  let li = logInfo' str
  liftIO $ outputLog True li
