module Data.Env where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Code
import Data.Constraint
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LLVM
import Data.List (find)
import Data.Log
import Data.LowType
import qualified Data.PQueue.Min as Q
import Data.Platform
import Data.Primitive
import qualified Data.Set as S
import Data.Size
import Data.Term
import qualified Data.Text as T
import Data.Tree
import Data.Version (showVersion)
import Data.WeakTerm
import Path
import Path.IO
import Paths_neut (version)
import System.Directory (createDirectoryIfMissing)
import System.Info
import qualified Text.Show.Pretty as Pr

type ConstraintQueue =
  Q.MinQueue EnrichedConstraint

data VisitInfo
  = VisitInfoActive
  | VisitInfoFinish

type TypeEnv =
  IntMap.IntMap TermPlus

data Env = Env
  { count :: Int,
    shouldColorize :: Bool,
    shouldCancelAlloc :: Bool,
    endOfEntry :: String,
    --
    -- parse
    --
    phase :: Int,
    notationEnv :: Map.HashMap T.Text [(TreePlus, TreePlus)],
    constantSet :: S.Set T.Text,
    fileEnv :: Map.HashMap (Path Abs File) VisitInfo,
    traceEnv :: [Path Abs File],
    -- [("choice", [("left", 0), ("right", 1)]), ...]
    enumEnv :: Map.HashMap T.Text [(T.Text, Int)],
    -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
    revEnumEnv :: Map.HashMap T.Text (T.Text, Int),
    prefixEnv :: [T.Text],
    sectionEnv :: [T.Text],
    topNameEnv :: Map.HashMap T.Text Ident,
    --
    -- elaborate
    --
    weakTypeEnv :: IntMap.IntMap WeakTermPlus,
    constTypeEnv :: Map.HashMap T.Text TermPlus,
    constraintEnv :: [PreConstraint],
    constraintQueue :: ConstraintQueue,
    substEnv :: IntMap.IntMap WeakTermPlus,
    opaqueEnv :: S.Set Ident,
    --
    -- clarify
    --
    typeEnv :: TypeEnv,
    codeEnv :: Map.HashMap T.Text Definition,
    --
    -- LLVM
    --
    llvmEnv :: Map.HashMap T.Text ([Ident], LLVM),
    declEnv :: Map.HashMap T.Text ([LowType], LowType),
    nopFreeSet :: S.Set Int
  }

initialEnv :: Env
initialEnv =
  Env
    { count = 0,
      shouldColorize = True,
      shouldCancelAlloc = True,
      endOfEntry = "",
      phase = 0,
      notationEnv = Map.empty,
      constantSet = S.empty,
      enumEnv = Map.empty,
      fileEnv = Map.empty,
      traceEnv = [],
      revEnumEnv = Map.empty,
      topNameEnv = Map.empty,
      prefixEnv = [],
      sectionEnv = [],
      weakTypeEnv = IntMap.empty,
      typeEnv = IntMap.empty,
      constTypeEnv = Map.empty,
      codeEnv = Map.empty,
      llvmEnv = Map.empty,
      declEnv =
        Map.fromList
          [ ("malloc", ([LowTypeInt 64], voidPtr)),
            ("free", ([voidPtr], LowTypeVoid))
          ],
      constraintEnv = [],
      constraintQueue = Q.empty,
      substEnv = IntMap.empty,
      opaqueEnv = S.empty,
      nopFreeSet = S.empty
    }

newtype Error
  = Error [Log]
  deriving (Show)

instance Exception Error

type WithEnv a =
  StateT Env IO a

evalWithEnv :: WithEnv a -> Env -> IO (Either Error a)
evalWithEnv c env = do
  resultOrErr <- try $ runStateT c env
  case resultOrErr of
    Left err ->
      return $ Left err
    Right (result, _) ->
      return $ Right result

{-# INLINE newCount #-}
newCount :: WithEnv Int
newCount = do
  i <- gets count
  modify (\e -> e {count = i + 1})
  if i + 1 == 0
    then raiseCritical' "counter exhausted"
    else return i

{-# INLINE newNameWith #-}
newNameWith :: Ident -> WithEnv Ident
newNameWith (I (s, _)) = do
  j <- newCount
  return $ I (s, j)

{-# INLINE newNameWith' #-}
newNameWith' :: T.Text -> WithEnv Ident
newNameWith' s = do
  i <- newCount
  return $ I (s, i)

{-# INLINE newNameWith'' #-}
newNameWith'' :: T.Text -> WithEnv Ident
newNameWith'' s = do
  i <- newCount
  return $ I ("(" <> s <> "-" <> T.pack (show i) <> ")", i)

{-# INLINE newTextWith #-}
newTextWith :: T.Text -> WithEnv T.Text
newTextWith s = do
  i <- newCount
  return $ "(" <> s <> "-" <> T.pack (show i) <> ")"

{-# INLINE newAster #-}
newAster :: Hint -> WithEnv WeakTermPlus
newAster m = do
  i <- newCount
  return (m, WeakTermAster i)

getOS :: WithEnv OS
getOS =
  case os of
    "linux" ->
      return OSLinux
    "darwin" ->
      return OSDarwin
    s ->
      raiseCritical' $ "unsupported target os: " <> T.pack (show s)

getArch :: WithEnv Arch
getArch =
  case arch of
    "x86_64" ->
      return Arch64
    "aarch64" ->
      return ArchAArch64
    s ->
      raiseCritical' $ "unsupported target arch: " <> T.pack (show s)

{-# INLINE newDataUpsilonWith #-}
newDataUpsilonWith :: Hint -> T.Text -> WithEnv (Ident, DataPlus)
newDataUpsilonWith m name = do
  x <- newNameWith' name
  return (x, (m, DataUpsilon x))

insTypeEnv :: Int -> TermPlus -> WithEnv ()
insTypeEnv x t =
  modify (\e -> e {typeEnv = IntMap.insert x t (typeEnv e)})

insTypeEnv' :: Int -> TermPlus -> TypeEnv -> TypeEnv
insTypeEnv' =
  IntMap.insert

lookupTypeEnv :: Hint -> Int -> T.Text -> WithEnv TermPlus
lookupTypeEnv m x name = do
  tenv <- gets typeEnv
  case IntMap.lookup x tenv of
    Just t ->
      return t
    Nothing ->
      raiseCritical m $
        "the variable `" <> name <> "` is not found in the type environment."

lookupTypeEnv' :: Hint -> Ident -> TypeEnv -> WithEnv TermPlus
lookupTypeEnv' m (I (name, x)) tenv =
  case IntMap.lookup x tenv of
    Just t ->
      return t
    Nothing ->
      raiseCritical m $
        "the variable `" <> name <> "` is not found in the type environment."

insConstTypeEnv :: T.Text -> TermPlus -> WithEnv ()
insConstTypeEnv x t =
  modify (\e -> e {constTypeEnv = Map.insert x t (constTypeEnv e)})

lookupConstTypeEnv :: Hint -> T.Text -> WithEnv TermPlus
lookupConstTypeEnv m x
  | Just _ <- asLowTypeMaybe x =
    return (m, TermTau)
  | Just op <- asUnaryOpMaybe x =
    unaryOpToType m op
  | Just op <- asBinaryOpMaybe x =
    binaryOpToType m op
  | Just lowType <- asArrayAccessMaybe x =
    arrayAccessToType m lowType
  | otherwise = do
    ctenv <- gets constTypeEnv
    case Map.lookup x ctenv of
      Just t -> return t
      Nothing ->
        raiseCritical m $
          "the constant `" <> x <> "` is not found in the type environment."

lowTypeToType :: Hint -> LowType -> WithEnv TermPlus
lowTypeToType m lowType =
  case lowType of
    LowTypeInt s ->
      return (m, TermConst (showIntSize s))
    LowTypeFloat s ->
      return (m, TermConst (showFloatSize s))
    LowTypeBool ->
      return (m, TermEnum "bool")
    _ ->
      raiseCritical m "invalid argument passed to lowTypeToType"

unaryOpToType :: Hint -> UnaryOp -> WithEnv TermPlus
unaryOpToType m op = do
  let (dom, cod) = unaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x <- newNameWith'' "_"
  let xts = [(m, x, dom')]
  return (m, TermPi xts cod')

binaryOpToType :: Hint -> BinaryOp -> WithEnv TermPlus
binaryOpToType m op = do
  let (dom, cod) = binaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x1 <- newNameWith'' "_"
  x2 <- newNameWith'' "_"
  let xts = [(m, x1, dom'), (m, x2, dom')]
  return (m, TermPi xts cod')

arrayAccessToType :: Hint -> LowType -> WithEnv TermPlus
arrayAccessToType m lowType = do
  t <- lowTypeToType m lowType
  k <- lowTypeToArrayKind m lowType
  idx <- newNameWith' "i"
  len <- newNameWith' "n"
  arrName <- newNameWith'' "_"
  let int64 = (m, TermConst (showIntSize 64))
  let arr = (m, TermArray (m, TermUpsilon len) k)
  let xts = [(m, idx, int64), (m, len, int64), (m, arrName, arr)]
  x4 <- newNameWith'' "_"
  x5 <- newNameWith'' "_"
  cod <- termSigma m [(m, x4, arr), (m, x5, t)]
  return (m, TermPi xts cod)

inferKind :: Hint -> ArrayKind -> WithEnv TermPlus
inferKind m arrayKind =
  case arrayKind of
    ArrayKindInt size ->
      return (m, TermConst (showIntSize size))
    ArrayKindFloat size ->
      return (m, TermConst (showFloatSize size))
    _ ->
      raiseCritical m "inferKind for void-pointer"

termSigma :: Hint -> [IdentPlus] -> WithEnv TermPlus
termSigma m xts = do
  z <- newNameWith' "internal.sigma-tau"
  let vz = (m, TermUpsilon z)
  k <- newNameWith'' "sigma"
  let yts = [(m, z, (m, TermTau)), (m, k, (m, TermPi xts vz))]
  return (m, TermPi yts vz)

insEnumEnv :: Hint -> T.Text -> [(T.Text, Int)] -> WithEnv ()
insEnumEnv m name xis = do
  eenv <- gets enumEnv
  let definedEnums = Map.keys eenv ++ map fst (concat (Map.elems eenv))
  case find (`elem` definedEnums) $ name : map fst xis of
    Just x ->
      raiseError m $ "the constant `" <> x <> "` is already defined [ENUM]"
    _ -> do
      let (xs, is) = unzip xis
      let rev = Map.fromList $ zip xs (zip (repeat name) is)
      modify
        ( \e ->
            e
              { enumEnv = Map.insert name xis (enumEnv e),
                revEnumEnv = rev `Map.union` revEnumEnv e
              }
        )

isConstant :: T.Text -> WithEnv Bool
isConstant name
  | Just (LowTypeInt _) <- asLowTypeMaybe name =
    return True
  | Just (LowTypeFloat _) <- asLowTypeMaybe name =
    return True
  | Just _ <- asUnaryOpMaybe name =
    return True
  | Just _ <- asBinaryOpMaybe name =
    return True
  | Just _ <- asArrayAccessMaybe name =
    return True
  | otherwise = do
    set <- gets constantSet
    return $ S.member name set

-- for debug
p :: String -> WithEnv ()
p s =
  liftIO $ putStrLn s

p' :: (Show a) => a -> WithEnv ()
p' s =
  liftIO $ putStrLn $ Pr.ppShow s

lowTypeToArrayKind :: Hint -> LowType -> WithEnv ArrayKind
lowTypeToArrayKind m lowType =
  case lowTypeToArrayKindMaybe lowType of
    Just k ->
      return k
    Nothing ->
      raiseCritical m "Infer.lowTypeToArrayKind"

raiseError :: Hint -> T.Text -> WithEnv a
raiseError m text =
  throw $ Error [logError (getPosInfo m) text]

raiseError' :: T.Text -> WithEnv a
raiseError' text =
  throw $ Error [logError' text]

raiseCritical :: Hint -> T.Text -> WithEnv a
raiseCritical m text =
  throw $ Error [logCritical (getPosInfo m) text]

raiseCritical' :: T.Text -> WithEnv a
raiseCritical' text =
  throw $ Error [logCritical' text]

getCurrentFilePath :: WithEnv (Path Abs File)
getCurrentFilePath = do
  tenv <- gets traceEnv
  return $ head tenv

getCurrentDirPath :: WithEnv (Path Abs Dir)
getCurrentDirPath =
  parent <$> getCurrentFilePath

getLibraryDirPath :: WithEnv (Path Abs Dir)
getLibraryDirPath = do
  let ver = showVersion version
  relLibPath <- parseRelDir $ ".local/share/neut/" <> ver <> "/library"
  getDirPath relLibPath

getDirPath :: Path Rel Dir -> WithEnv (Path Abs Dir)
getDirPath base = do
  homeDirPath <- getHomeDir
  let path = homeDirPath </> base
  liftIO $ createDirectoryIfMissing True $ toFilePath path
  return path

note :: Hint -> T.Text -> WithEnv ()
note m str = do
  b <- gets shouldColorize
  eoe <- gets endOfEntry
  liftIO $ outputLog b eoe $ logNote (getPosInfo m) str

note' :: T.Text -> WithEnv ()
note' str = do
  b <- gets shouldColorize
  eoe <- gets endOfEntry
  liftIO $ outputLog b eoe $ logNote' str

note'' :: T.Text -> WithEnv ()
note'' str = do
  b <- gets shouldColorize
  liftIO $ outputLog' b $ logNote' str

warn :: PosInfo -> T.Text -> WithEnv ()
warn pos str = do
  b <- gets shouldColorize
  eoe <- gets endOfEntry
  liftIO $ outputLog b eoe $ logWarning pos str

insertConstant :: Hint -> T.Text -> WithEnv ()
insertConstant m x = do
  cset <- gets constantSet
  if S.member x cset
    then raiseError m $ "the constant `" <> x <> "` is already defined"
    else modify (\env -> env {constantSet = S.insert x (constantSet env)})
