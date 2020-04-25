module Data.Env where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Basic
import Data.Code
import Data.Constraint
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.LLVM
import Data.List (find)
import Data.Log
import qualified Data.PQueue.Min as Q
import Data.Primitive
import qualified Data.Set as S
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

data Env
  = Env
      { count :: Int,
        ppCount :: Int, -- count used only for pretty printing
        shouldColorize :: Bool,
        endOfEntry :: String,
        isCheck :: Bool,
        --
        -- parse
        --
        phase :: Int,
        target :: Maybe Target,
        -- list of reserved keywords
        keywordEnv :: S.Set T.Text,
        -- macro transformers
        notationEnv :: [(TreePlus, TreePlus)],
        constantSet :: S.Set T.Text,
        fileEnv :: Map.HashMap (Path Abs File) VisitInfo,
        traceEnv :: [Path Abs File],
        -- [("choice", [("left", 0), ("right", 1)]), ...]
        enumEnv :: Map.HashMap T.Text [(T.Text, Int)],
        -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
        revEnumEnv :: Map.HashMap T.Text (T.Text, Int),
        nameEnv :: Map.HashMap T.Text T.Text,
        -- [("foo.13", "foo"), ...] (as corresponding int)
        revNameEnv :: IntMap.IntMap Int,
        prefixEnv :: [T.Text],
        sectionEnv :: [T.Text],
        formationEnv :: IntMap.IntMap (Maybe WeakTermPlus),
        -- "stream" ~> ["stream", "other-record-type", "head", "tail", "other-destructor"]
        labelEnv :: Map.HashMap T.Text [T.Text],
        -- "list" ~> (cons, Pi (A : tau). A -> list A -> list A)
        indEnv :: IntMap.IntMap (Maybe [WeakIdentPlus]),
        -- "list:cons" ~> ("list", [0])
        revIndEnv :: Map.HashMap T.Text (Ident, [Int]),
        intactSet :: S.Set (Meta, T.Text),
        topNameEnv :: Map.HashMap T.Text Ident,
        --
        -- elaborate
        --
        -- const ~> (index of implicit arguments of the const)
        impEnv :: IntMap.IntMap [Int],
        weakTypeEnv :: IntMap.IntMap WeakTermPlus,
        constTypeEnv :: Map.HashMap T.Text TermPlus,
        constraintEnv :: [PreConstraint],
        constraintQueue :: ConstraintQueue,
        substEnv :: IntMap.IntMap WeakTermPlus,
        defEnv :: IntMap.IntMap TermPlus,
        holeEnv :: IntMap.IntMap (WeakTermPlus, WeakTermPlus),
        --
        -- clarify
        --
        -- f ~> thunk (lam (x1 ... xn) e)
        typeEnv :: TypeEnv,
        codeEnv :: Map.HashMap T.Text Definition,
        nameSet :: S.Set T.Text,
        chainEnv :: IntMap.IntMap [IdentPlus],
        --
        -- LLVM
        --
        llvmEnv :: Map.HashMap T.Text ([Ident], LLVM),
        -- external functions that must be declared in LLVM IR
        declEnv :: Map.HashMap T.Text ([LowType], LowType),
        nopFreeSet :: S.Set Int
      }

initialEnv :: Env
initialEnv =
  Env
    { count = 0,
      ppCount = 0,
      shouldColorize = False,
      isCheck = False,
      endOfEntry = "",
      phase = 0,
      target = Nothing,
      notationEnv = [],
      keywordEnv = S.empty,
      constantSet = S.empty,
      enumEnv = Map.empty,
      fileEnv = Map.empty,
      traceEnv = [],
      revEnumEnv = Map.empty,
      nameEnv = Map.empty,
      revNameEnv = IntMap.empty,
      revIndEnv = Map.empty,
      intactSet = S.empty,
      topNameEnv = Map.empty,
      prefixEnv = [],
      sectionEnv = [],
      formationEnv = IntMap.empty,
      indEnv = IntMap.empty,
      labelEnv = Map.empty,
      weakTypeEnv = IntMap.empty,
      typeEnv = IntMap.empty,
      constTypeEnv = Map.empty,
      impEnv = IntMap.empty,
      codeEnv = Map.empty,
      chainEnv = IntMap.empty,
      llvmEnv = Map.empty,
      declEnv =
        Map.fromList
          [ ("malloc", ([LowTypeInt 64], voidPtr)),
            ("free", ([voidPtr], LowTypeVoid))
          ],
      constraintEnv = [],
      constraintQueue = Q.empty,
      substEnv = IntMap.empty,
      defEnv = IntMap.empty,
      holeEnv = IntMap.empty,
      nameSet = S.empty,
      nopFreeSet = S.empty
    }

newtype Error
  = Error [Log]
  deriving (Show)

instance Exception Error

type WithEnv a =
  StateT Env IO a

whenCheck :: WithEnv () -> WithEnv ()
whenCheck f = do
  b <- gets isCheck
  when b f

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

newCountPP :: WithEnv Int
newCountPP = do
  i <- gets ppCount
  modify (\e -> e {ppCount = i + 1})
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

{-# INLINE newHole #-}
newHole :: Meta -> WithEnv WeakTermPlus
newHole m = do
  h <- newNameWith'' "hole"
  return (m, WeakTermHole h)

getTarget :: WithEnv Target
getTarget = do
  mtarget <- gets target
  case mtarget of
    Just t ->
      return t
    Nothing -> do
      currentOS <- getOS
      currentArch <- getArch
      return (currentOS, currentArch)

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
    s ->
      raiseCritical' $ "unsupported target arch: " <> T.pack (show s)

{-# INLINE newDataUpsilonWith #-}
newDataUpsilonWith :: Meta -> T.Text -> WithEnv (Ident, DataPlus)
newDataUpsilonWith m name = do
  x <- newNameWith' name
  return (x, (m, DataUpsilon x))

insTypeEnv :: Int -> TermPlus -> WithEnv ()
insTypeEnv x t =
  modify (\e -> e {typeEnv = IntMap.insert x t (typeEnv e)})

insTypeEnv' :: Int -> TermPlus -> TypeEnv -> TypeEnv
insTypeEnv' =
  IntMap.insert

lookupTypeEnv :: Meta -> Int -> T.Text -> WithEnv TermPlus
lookupTypeEnv m x name = do
  tenv <- gets typeEnv
  case IntMap.lookup x tenv of
    Just t ->
      return t
    Nothing ->
      raiseCritical m $
        "the variable `" <> name <> "` is not found in the type environment."

lookupTypeEnv' :: Meta -> Ident -> TypeEnv -> WithEnv TermPlus
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

lookupConstTypeEnv :: Meta -> T.Text -> WithEnv TermPlus
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

lowTypeToType :: Meta -> LowType -> WithEnv TermPlus
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

unaryOpToType :: Meta -> UnaryOp -> WithEnv TermPlus
unaryOpToType m op = do
  let (dom, cod) = unaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x <- newNameWith' "arg"
  let xts = [(m, x, dom')]
  return (m, termPi xts cod')

binaryOpToType :: Meta -> BinaryOp -> WithEnv TermPlus
binaryOpToType m op = do
  let (dom, cod) = binaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x1 <- newNameWith' "arg"
  x2 <- newNameWith' "arg"
  let xts = [(m, x1, dom'), (m, x2, dom')]
  return (m, termPi xts cod')

arrayAccessToType :: Meta -> LowType -> WithEnv TermPlus
arrayAccessToType m lowType = do
  t <- lowTypeToType m lowType
  k <- lowTypeToArrayKind m lowType
  x1 <- newNameWith' "arg"
  x2 <- newNameWith' "arg"
  x3 <- newNameWith' "arg"
  let int64 = (m, TermConst (showIntSize 64))
  let idx = (m, TermUpsilon x2)
  let arr = (m, TermArray idx k)
  let xts = [(m, x1, int64), (m, x2, int64), (m, x3, arr)]
  x4 <- newNameWith' "arg"
  x5 <- newNameWith' "arg"
  cod <- termSigma m [(m, x4, arr), (m, x5, t)]
  return (m, termPi xts cod)

weakTermSigma :: Meta -> [WeakIdentPlus] -> WithEnv WeakTermPlus
weakTermSigma m xts = do
  z <- newNameWith'' "sigma"
  let vz = (m, WeakTermUpsilon z)
  k <- newNameWith'' "sigma"
  let yts = [(m, z, (m, WeakTermTau)), (m, k, (m, weakTermPi xts vz))]
  return (m, weakTermPi yts vz)

termSigma :: Meta -> [IdentPlus] -> WithEnv TermPlus
termSigma m xts = do
  z <- newNameWith'' "sigma"
  let vz = (m, TermUpsilon z)
  k <- newNameWith'' "sigma"
  let yts = [(m, z, (m, TermTau)), (m, k, (m, termPi xts vz))]
  return (m, termPi yts vz)

insEnumEnv :: Meta -> T.Text -> [(T.Text, Int)] -> WithEnv ()
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

lowTypeToArrayKind :: Meta -> LowType -> WithEnv ArrayKind
lowTypeToArrayKind m lowType =
  case lowTypeToArrayKindMaybe lowType of
    Just k ->
      return k
    Nothing ->
      raiseCritical m "Infer.lowTypeToArrayKind"

raiseError :: Meta -> T.Text -> WithEnv a
raiseError m text =
  throw $ Error [logError (getPosInfo m) text]

raiseCritical :: Meta -> T.Text -> WithEnv a
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

note :: Meta -> T.Text -> WithEnv ()
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

lookupRevIndEnv :: Meta -> T.Text -> WithEnv (Ident, [Int])
lookupRevIndEnv m bi = do
  rienv <- gets revIndEnv
  case Map.lookup bi rienv of
    Nothing ->
      raiseCritical m $ "no such constructor defined: `" <> bi <> "`"
    Just val ->
      return val

insertConstant :: Meta -> T.Text -> WithEnv ()
insertConstant m x = do
  cset <- gets constantSet
  if S.member x cset
    then raiseError m $ "the constant `" <> x <> "` is already defined"
    else modify (\env -> env {constantSet = S.insert x (constantSet env)})
