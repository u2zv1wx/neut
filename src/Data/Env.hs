module Data.Env where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Basic
import Data.Comp
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.Log
import Data.LowComp
import Data.LowType
import Data.MetaTerm
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import Data.Version (showVersion)
import Data.WeakTerm
import Path
import Path.IO
import Paths_neut (version)
import System.Directory (createDirectoryIfMissing)
import qualified Text.Show.Pretty as Pr

data VisitInfo
  = VisitInfoActive
  | VisitInfoFinish

data Env = Env
  { count :: Int,
    shouldColorize :: Bool,
    shouldCancelAlloc :: Bool,
    endOfEntry :: String,
    --
    -- Preprocess
    --
    topMetaNameEnv :: Map.HashMap T.Text Ident,
    metaTermCtx :: SubstMetaTerm,
    --
    -- parse
    --
    phase :: Int,
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
    suspendedConstraintEnv :: [SuspendedConstraint],
    substEnv :: IntMap.IntMap WeakTermPlus,
    -- opaqueEnv :: S.Set Ident,
    --
    -- clarify
    --
    codeEnv :: Map.HashMap T.Text Definition,
    --
    -- LLVM
    --
    lowCompEnv :: Map.HashMap T.Text ([Ident], LowComp),
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
      topMetaNameEnv = Map.empty,
      metaTermCtx = IntMap.empty,
      phase = 0,
      constantSet = S.empty,
      enumEnv = Map.empty,
      fileEnv = Map.empty,
      traceEnv = [],
      revEnumEnv = Map.empty,
      topNameEnv = Map.empty,
      prefixEnv = [],
      sectionEnv = [],
      weakTypeEnv = IntMap.empty,
      constTypeEnv = Map.empty,
      codeEnv = Map.empty,
      lowCompEnv = Map.empty,
      declEnv =
        Map.fromList
          [ ("malloc", ([voidPtr], voidPtr)),
            ("free", ([voidPtr], voidPtr))
          ],
      constraintEnv = [],
      -- constraintQueue = Q.empty,
      suspendedConstraintEnv = [],
      substEnv = IntMap.empty,
      -- opaqueEnv = S.empty,
      nopFreeSet = S.empty
    }

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

--
-- generating new symbols using count
--

{-# INLINE newCount #-}
newCount :: WithEnv Int
newCount = do
  i <- gets count
  modify (\e -> e {count = i + 1})
  if i + 1 == 0
    then raiseCritical' "counter exhausted"
    else return i

{-# INLINE newIdentFromText #-}
newIdentFromText :: T.Text -> WithEnv Ident
newIdentFromText s = do
  i <- newCount
  return $ I (s, i)

{-# INLINE newIdentFromIdent #-}
newIdentFromIdent :: Ident -> WithEnv Ident
newIdentFromIdent x =
  newIdentFromText (asText x)

{-# INLINE newText #-}
newText :: WithEnv T.Text
newText = do
  i <- newCount
  return $ ";" <> T.pack (show i)

{-# INLINE newAster #-}
newAster :: Hint -> WithEnv WeakTermPlus
newAster m = do
  i <- newCount
  return (m, WeakTermAster i)

{-# INLINE newValueUpsilonWith #-}
newValueUpsilonWith :: Hint -> T.Text -> WithEnv (Ident, ValuePlus)
newValueUpsilonWith m name = do
  x <- newIdentFromText name
  return (x, (m, ValueUpsilon x))

--
-- obtain information from the environment
--

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

--
-- output
--

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

-- for debug
p :: String -> WithEnv ()
p s =
  liftIO $ putStrLn s

p' :: (Show a) => a -> WithEnv ()
p' s =
  liftIO $ putStrLn $ Pr.ppShow s
