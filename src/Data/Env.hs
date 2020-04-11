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
import Data.Version (showVersion)
import Data.WeakTerm
import Paths_neut (version)

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

type RuleEnv = Map.HashMap T.Text (Maybe [TextPlus])

type UnivInstEnv = IntMap.IntMap (S.Set Int)

type TypeEnvKey = Either Int T.Text

type TypeEnv = Map.HashMap TypeEnvKey TermPlus

data Env =
  Env
    { count :: Int
    , ppCount :: Int -- count used only for pretty printing
    , shouldColorize :: Bool
    , endOfEntry :: String
    , isCheck :: Bool
    --
    -- parse
    --
    , phase :: Int
    , target :: Maybe Target
    -- list of reserved keywords
    , keywordEnv :: S.Set T.Text
    -- macro transformers
    , notationEnv :: [(TreePlus, TreePlus)]
    , constantSet :: S.Set T.Text
    -- path ~> identifiers defined in the file at toplevel
    , fileEnv :: FileEnv
    , traceEnv :: [Path Abs File]
    -- [("choice", [("left", 0), ("right", 1)]), ...]
    , enumEnv :: Map.HashMap T.Text [(T.Text, Int)]
    -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
    , revEnumEnv :: Map.HashMap T.Text (T.Text, Int)
    , nameEnv :: Map.HashMap T.Text T.Text
    -- [("foo.13", "foo"), ...] (as corresponding int)
    , revNameEnv :: IntMap.IntMap Int
    , prefixEnv :: [T.Text]
    , sectionEnv :: [T.Text]
    , formationEnv :: Map.HashMap T.Text (Maybe WeakTermPlus)
    -- "stream" ~> ["stream", "other-record-type", "head", "tail", "other-destructor"]
    , labelEnv :: Map.HashMap T.Text [T.Text]
    -- "list" ~> (cons, Pi (A : tau). A -> list A -> list A)
    , indEnv :: RuleEnv
    -- "list:cons" ~> ("list", [0])
    , revIndEnv :: Map.HashMap T.Text (T.Text, [Int])
    , intactSet :: S.Set (Meta, T.Text)
    --
    -- elaborate
    --
    -- const ~> (index of implicit arguments of the const)
    , impEnv :: Map.HashMap T.Text [Int]
    , weakTypeEnv :: IntMap.IntMap WeakTermPlus
    , typeEnv :: TypeEnv
    , constraintEnv :: [PreConstraint]
    , constraintQueue :: ConstraintQueue
    -- metavar ~> beta-equivalent weakterm
    , substEnv :: IntMap.IntMap WeakTermPlus
    , zetaEnv :: IntMap.IntMap (WeakTermPlus, WeakTermPlus)
    --
    -- clarify
    --
    , cacheEnv :: Map.HashMap T.Text (Either TermPlus CodePlus)
    -- f ~> thunk (lam (x1 ... xn) e)
    , codeEnv :: Map.HashMap T.Text Definition
    , nameSet :: S.Set T.Text
    , chainEnv :: Map.HashMap TypeEnvKey ([Data.Term.IdentifierPlus], TermPlus)
    --
    -- LLVM
    --
    , llvmEnv :: Map.HashMap T.Text ([Identifier], LLVM)
    -- external functions that must be declared in LLVM IR
    , declEnv :: Map.HashMap T.Text ([LowType], LowType)
    , nopFreeSet :: S.Set Int
    }

initialEnv :: Env
initialEnv =
  Env
    { count = 0
    , ppCount = 0
    , shouldColorize = False
    , isCheck = False
    , endOfEntry = ""
    , phase = 0
    , target = Nothing
    , notationEnv = []
    , keywordEnv = S.empty
    , constantSet = S.empty
    , enumEnv = Map.empty
    , fileEnv = Map.empty
    , traceEnv = []
    , revEnumEnv = Map.empty
    , nameEnv = Map.empty
    , revNameEnv = IntMap.empty
    , revIndEnv = Map.empty
    , intactSet = S.empty
    , prefixEnv = []
    , sectionEnv = []
    , formationEnv = Map.empty
    , indEnv = Map.empty
    , labelEnv = Map.empty
    , impEnv = Map.empty
    , weakTypeEnv = IntMap.empty
    , typeEnv = Map.empty
    , cacheEnv = Map.empty
    , codeEnv = Map.empty
    , chainEnv = Map.empty
    , llvmEnv = Map.empty
    , declEnv =
        Map.fromList
          [ ("malloc", ([LowTypeIntS 64], voidPtr))
          , ("free", ([voidPtr], LowTypeVoid))
          ]
    , constraintEnv = []
    , constraintQueue = Q.empty
    , substEnv = IntMap.empty
    , zetaEnv = IntMap.empty
    , nameSet = S.empty
    , nopFreeSet = S.empty
    }

type WithEnv a = StateT Env (ExceptT [Log] IO) a

whenCheck :: WithEnv () -> WithEnv ()
whenCheck f = do
  b <- gets isCheck
  when b f

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
  return $ I ("(" <> s <> "-" <> T.pack (show i) <> ")", i)

newTextWith :: T.Text -> WithEnv T.Text
newTextWith s = do
  i <- newCount
  return $ "(" <> s <> "-" <> T.pack (show i) <> ")"

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

insTypeEnv :: TypeEnvKey -> TermPlus -> WithEnv ()
insTypeEnv x t = modify (\e -> e {typeEnv = Map.insert x t (typeEnv e)})

insTypeEnv' :: TypeEnvKey -> TermPlus -> TypeEnv -> TypeEnv
insTypeEnv' x t tenv = Map.insert x t tenv

lookupTypeEnv :: Meta -> TypeEnvKey -> T.Text -> WithEnv TermPlus
lookupTypeEnv m x name = do
  tenv <- gets typeEnv
  case Map.lookup x tenv of
    Just t -> return t
    Nothing ->
      raiseCritical m $
      "the constant `" <> name <> "` is not found in the type environment."

lookupTypeEnv' :: Meta -> TypeEnvKey -> TypeEnv -> T.Text -> WithEnv TermPlus
lookupTypeEnv' m (Right s) _ _
  | Just _ <- asLowTypeMaybe s = return (m, TermTau)
  | Just op <- asUnaryOpMaybe s = unaryOpToType m op
  | Just op <- asBinaryOpMaybe s = binaryOpToType m op
  | Just lowType <- asArrayAccessMaybe s = arrayAccessToType m lowType
lookupTypeEnv' m key tenv name = do
  case Map.lookup key tenv of
    Just t -> return t
    Nothing ->
      raiseCritical m $
      "the constant `" <> name <> "` is not found in the type environment."

lowTypeToType :: Meta -> LowType -> WithEnv TermPlus
lowTypeToType m (LowTypeIntS s) = return (m, TermEnum (EnumTypeIntS s))
lowTypeToType m (LowTypeIntU s) = return (m, TermEnum (EnumTypeIntU s))
lowTypeToType m (LowTypeFloat s) = do
  return (m, TermConst $ "f" <> T.pack (show (sizeAsInt s)))
lowTypeToType m _ = raiseCritical m "invalid argument passed to lowTypeToType"

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
  let u64 = (m, TermEnum (EnumTypeIntU 64))
  let idx = (m, TermUpsilon x2)
  let arr = (m, TermArray idx k)
  let xts = [(m, x1, u64), (m, x2, u64), (m, x3, arr)]
  x4 <- newNameWith' "arg"
  x5 <- newNameWith' "arg"
  cod <- termSigma m [(m, x4, arr), (m, x5, t)]
  return (m, termPi xts cod)

weakTermSigma :: Meta -> [Data.WeakTerm.IdentifierPlus] -> WithEnv WeakTermPlus
weakTermSigma m xts = do
  z <- newNameWith'' "sigma"
  let vz = (m, WeakTermUpsilon z)
  k <- newNameWith'' "sigma"
  let yts = [(m, z, (m, WeakTermTau)), (m, k, (m, weakTermPi xts vz))]
  return (m, weakTermPi yts vz)

termSigma :: Meta -> [Data.Term.IdentifierPlus] -> WithEnv TermPlus
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
        (\e ->
           e
             { enumEnv = Map.insert name xis (enumEnv e)
             , revEnumEnv = rev `Map.union` (revEnumEnv e)
             })

isConstant :: T.Text -> WithEnv Bool
isConstant name
  | name == "f16" = return True
  | name == "f32" = return True
  | name == "f64" = return True
  | Just _ <- asUnaryOpMaybe name = return True
  | Just _ <- asBinaryOpMaybe name = return True
  | Just _ <- asArrayAccessMaybe name = return True
  | otherwise = do
    set <- gets constantSet
    return $ S.member name set

-- for debug
p :: String -> WithEnv ()
p s = liftIO $ putStrLn s

p' :: (Show a) => a -> WithEnv ()
p' s = liftIO $ putStrLn $ Pr.ppShow s

pp :: WeakTermPlus -> WithEnv ()
pp e = liftIO $ TIO.putStrLn $ toText e

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
  let ver = showVersion version
  relLibPath <- parseRelDir $ ".local/share/neut/" <> ver <> "/library"
  return $ homeDirPath </> relLibPath

note :: Meta -> T.Text -> WithEnv ()
note m str = do
  b <- gets shouldColorize
  eoe <- gets endOfEntry
  liftIO $ outputLog b eoe $ logInfo (getPosInfo m) str

note' :: T.Text -> WithEnv ()
note' str = do
  b <- gets shouldColorize
  eoe <- gets endOfEntry
  liftIO $ outputLog b eoe $ logInfo' str

warn :: PosInfo -> T.Text -> WithEnv ()
warn pos str = do
  b <- gets shouldColorize
  eoe <- gets endOfEntry
  liftIO $ outputLog b eoe $ logWarning pos str

lookupRevIndEnv :: Meta -> T.Text -> WithEnv (T.Text, [Int])
lookupRevIndEnv m bi = do
  rienv <- gets revIndEnv
  case Map.lookup bi rienv of
    Nothing -> raiseCritical m $ "no such constructor defined: `" <> bi <> "`"
    Just val -> return val
