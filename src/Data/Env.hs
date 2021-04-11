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
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Version (showVersion)
import Data.WeakTerm
import Path
import Path.IO
import Paths_neut (version)
import System.Console.ANSI
import System.Directory (createDirectoryIfMissing)
import System.Exit
import qualified Text.Show.Pretty as Pr

type Compiler a =
  StateT Env IO a

data VisitInfo
  = VisitInfoActive
  | VisitInfoFinish

data Env = Env
  { count :: Int,
    shouldColorize :: Bool,
    shouldDisplayLogLocation :: Bool,
    shouldDisplayLogLevel :: Bool,
    shouldDisplayLogText :: Bool,
    shouldDisplayLogFooter :: Bool,
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
    fileEnv :: Map.HashMap (Path Abs File) VisitInfo,
    traceEnv :: [Path Abs File],
    -- [("choice", [("left", 0), ("right", 1)]), ...]
    enumEnv :: Map.HashMap T.Text [(T.Text, Int)],
    -- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
    revEnumEnv :: Map.HashMap T.Text (T.Text, Int),
    dataEnv :: Map.HashMap T.Text [T.Text],
    constructorEnv :: Map.HashMap T.Text (Int, Int),
    prefixEnv :: [T.Text],
    nsEnv :: [(T.Text, T.Text)],
    sectionEnv :: [T.Text],
    topNameEnv :: Map.HashMap T.Text Ident,
    --
    -- elaborate
    --
    weakTypeEnv :: IntMap.IntMap WeakTermPlus,
    constTypeEnv :: Map.HashMap T.Text TermPlus,
    holeEnv :: IntMap.IntMap (WeakTermPlus, WeakTermPlus),
    constraintEnv :: [Constraint],
    suspendedConstraintEnv :: SuspendedConstraintQueue,
    substEnv :: IntMap.IntMap WeakTermPlus,
    opaqueEnv :: S.Set Ident,
    --
    -- clarify
    --
    defEnv :: Map.HashMap T.Text (IsReducible, [Ident], CompPlus),
    --
    -- LLVM
    --
    lowDefEnv :: Map.HashMap T.Text ([Ident], LowComp),
    declEnv :: Map.HashMap T.Text ([LowType], LowType),
    nopFreeSet :: S.Set Int
  }

initialEnv :: Env
initialEnv =
  Env
    { count = 0,
      shouldColorize = True,
      shouldDisplayLogLocation = True,
      shouldDisplayLogLevel = True,
      shouldDisplayLogText = True,
      shouldDisplayLogFooter = True,
      shouldCancelAlloc = True,
      endOfEntry = "",
      topMetaNameEnv = Map.empty,
      metaTermCtx = IntMap.empty,
      nsEnv = [],
      enumEnv = Map.empty,
      fileEnv = Map.empty,
      holeEnv = IntMap.empty,
      traceEnv = [],
      revEnumEnv = Map.empty,
      dataEnv = Map.empty,
      constructorEnv = Map.empty,
      topNameEnv = Map.empty,
      prefixEnv = [],
      sectionEnv = [],
      weakTypeEnv = IntMap.empty,
      constTypeEnv = Map.empty,
      defEnv = Map.empty,
      lowDefEnv = Map.empty,
      declEnv =
        Map.fromList
          [ ("malloc", ([voidPtr], voidPtr)),
            ("free", ([voidPtr], voidPtr))
          ],
      constraintEnv = [],
      suspendedConstraintEnv = Q.empty,
      substEnv = IntMap.empty,
      opaqueEnv = S.empty,
      nopFreeSet = S.empty
    }

runCompiler :: Compiler a -> Env -> IO a
runCompiler c env = do
  resultOrErr <- try $ runStateT c env
  case resultOrErr of
    Left (Error err) ->
      foldr (>>) (exitWith (ExitFailure 1)) (map (outputLog env) err)
    Right (result, _) ->
      return result

--
-- generating new symbols using count
--

{-# INLINE newCount #-}
newCount :: Compiler Int
newCount = do
  i <- gets count
  modify (\e -> e {count = i + 1})
  if i + 1 == 0
    then raiseCritical' "counter exhausted"
    else return i

{-# INLINE newIdentFromText #-}
newIdentFromText :: T.Text -> Compiler Ident
newIdentFromText s = do
  i <- newCount
  return $ I (s, i)

{-# INLINE newIdentFromIdent #-}
newIdentFromIdent :: Ident -> Compiler Ident
newIdentFromIdent x =
  newIdentFromText (asText x)

{-# INLINE newText #-}
newText :: Compiler T.Text
newText = do
  i <- newCount
  return $ ";" <> T.pack (show i)

{-# INLINE newAster #-}
newAster :: Hint -> Compiler WeakTermPlus
newAster m = do
  i <- newCount
  return (m, WeakTermAster i)

{-# INLINE newValueVarLocalWith #-}
newValueVarLocalWith :: Hint -> T.Text -> Compiler (Ident, ValuePlus)
newValueVarLocalWith m name = do
  x <- newIdentFromText name
  return (x, (m, ValueVarLocal x))

--
-- obtain information from the environment
--

getCurrentFilePath :: Compiler (Path Abs File)
getCurrentFilePath = do
  tenv <- gets traceEnv
  return $ head tenv

getCurrentDirPath :: Compiler (Path Abs Dir)
getCurrentDirPath =
  parent <$> getCurrentFilePath

getLibraryDirPath :: Compiler (Path Abs Dir)
getLibraryDirPath = do
  let ver = showVersion version
  relLibPath <- parseRelDir $ ".local/share/neut/" <> ver <> "/library"
  getDirPath relLibPath

getDirPath :: Path Rel Dir -> Compiler (Path Abs Dir)
getDirPath base = do
  homeDirPath <- getHomeDir
  let path = homeDirPath </> base
  liftIO $ createDirectoryIfMissing True $ toFilePath path
  return path

--
-- log
--

outputLog :: Env -> Log -> IO ()
outputLog env (mpos, l, t) = do
  when (shouldDisplayLogLocation env) $
    outputLogLocation (shouldColorize env) mpos
  when (shouldDisplayLogLevel env) $
    outputLogLevel (shouldColorize env) l
  when (shouldDisplayLogText env) $
    outputLogText t (logLevelToPad env l)
  when (shouldDisplayLogFooter env) $
    outputFooter (endOfEntry env)

outputLogLocation :: Bool -> Maybe PosInfo -> IO ()
outputLogLocation colorFlag mpos =
  case mpos of
    Nothing ->
      return ()
    Just (path, loc) ->
      withSGR colorFlag [SetConsoleIntensity BoldIntensity] $ do
        TIO.putStr $ T.pack (showPosInfo path loc)
        TIO.putStrLn ":"

outputFooter :: String -> IO ()
outputFooter eoe =
  if eoe == ""
    then return ()
    else putStrLn eoe

outputPosInfo :: Bool -> PosInfo -> IO ()
outputPosInfo b (path, loc) =
  withSGR b [SetConsoleIntensity BoldIntensity] $ do
    TIO.putStr $ T.pack (showPosInfo path loc)
    TIO.putStrLn ":"

outputLogLevel :: Bool -> LogLevel -> IO ()
outputLogLevel b l =
  withSGR b (logLevelToSGR l) $ do
    TIO.putStr $ logLevelToText l
    TIO.putStr ": "

outputLogText :: T.Text -> T.Text -> IO ()
outputLogText str pad =
  TIO.putStrLn $ stylizeLogText str pad

logLevelToPad :: Env -> LogLevel -> T.Text
logLevelToPad env level =
  if shouldDisplayLogLevel env
    then T.replicate (T.length (logLevelToText level) + 2) " "
    else ""

stylizeLogText :: T.Text -> T.Text -> T.Text
stylizeLogText str pad = do
  let ls = T.lines str
  if null ls
    then str
    else T.intercalate "\n" $ head ls : map (pad <>) (tail ls)

withSGR :: Bool -> [SGR] -> IO () -> IO ()
withSGR b arg f =
  if b
    then setSGR arg >> f >> setSGR [Reset]
    else f

note :: Hint -> T.Text -> Compiler ()
note m str = do
  env <- get
  liftIO $ outputLog env $ logNote (getPosInfo m) str

note' :: T.Text -> Compiler ()
note' str = do
  env <- get
  liftIO $ outputLog env $ logNote' str

warn :: PosInfo -> T.Text -> Compiler ()
warn pos str = do
  env <- get
  liftIO $ outputLog env $ logWarning pos str

outputPass :: String -> IO ()
outputPass str = do
  outputLog initialEnv (Nothing, LogLevelPass, T.pack str)

outputFail :: String -> IO ()
outputFail str = do
  outputLog initialEnv (Nothing, LogLevelFail, T.pack str)

-- for debug
p :: String -> Compiler ()
p s =
  liftIO $ putStrLn s

p' :: (Show a) => a -> Compiler ()
p' s =
  liftIO $ putStrLn $ Pr.ppShow s
