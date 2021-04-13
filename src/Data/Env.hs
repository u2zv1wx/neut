module Data.Env where

import Control.Exception.Safe
import Data.Basic
import Data.Comp
import qualified Data.HashMap.Lazy as Map
import Data.IORef
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
import System.IO.Unsafe (unsafePerformIO)
import qualified Text.Show.Pretty as Pr

data VisitInfo
  = VisitInfoActive
  | VisitInfoFinish

-- data Env = Env
--   {
--   }

-- shouldColorize :: Bool,
-- shouldDisplayLogLocation :: Bool,
-- shouldDisplayLogLevel :: Bool,
-- shouldDisplayLogText :: Bool,
-- shouldDisplayLogFooter :: Bool,
-- shouldCancelAlloc :: Bool,
-- endOfEntry :: String,
--
-- Preprocess
--
-- topMetaNameEnv :: Map.HashMap T.Text Ident,
-- metaTermCtx :: SubstMetaTerm,
--
-- parse
--
-- fileEnv :: Map.HashMap (Path Abs File) VisitInfo,
-- traceEnv :: [Path Abs File],
-- [("choice", [("left", 0), ("right", 1)]), ...]
-- enumEnv :: Map.HashMap T.Text [(T.Text, Int)],
-- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
-- revEnumEnv :: Map.HashMap T.Text (T.Text, Int),
-- dataEnv :: Map.HashMap T.Text [T.Text],
-- constructorEnv :: Map.HashMap T.Text (Int, Int),
-- prefixEnv :: [T.Text],
-- nsEnv :: [(T.Text, T.Text)],
-- sectionEnv :: [T.Text],
-- topNameEnv :: Map.HashMap T.Text Ident,
--
-- elaborate
--
-- weakTypeEnv :: IntMap.IntMap WeakTermPlus,
-- constTypeEnv :: Map.HashMap T.Text TermPlus,
-- holeEnv :: IntMap.IntMap (WeakTermPlus, WeakTermPlus),
-- constraintEnv :: [Constraint],
-- suspendedConstraintEnv :: SuspendedConstraintQueue,
-- substEnv :: IntMap.IntMap WeakTermPlus,
-- opaqueEnv :: S.Set Ident,
--
-- clarify
--
-- defEnv :: Map.HashMap T.Text (IsReducible, [Ident], CompPlus),
--
-- LLVM
--
-- lowDefEnv :: Map.HashMap T.Text ([Ident], LowComp),
-- declEnv :: Map.HashMap T.Text ([LowType], LowType),
-- nopFreeSet :: S.Set Int

-- initialEnv :: Env
-- initialEnv =
--   Env
--   -- shouldColorize = True,
--   -- shouldDisplayLogLocation = True,
--   -- shouldDisplayLogLevel = True,
--   -- shouldDisplayLogText = True,
--   -- shouldDisplayLogFooter = True,
--   -- shouldCancelAlloc = True,
--   -- endOfEntry = "",
--   -- topMetaNameEnv = Map.empty,
--   -- metaTermCtx = IntMap.empty,
--   -- nsEnv = [],
--   -- enumEnv = Map.empty,
--   -- fileEnv = Map.empty,
--   -- holeEnv = IntMap.empty,
--   -- traceEnv = [],
--   -- revEnumEnv = Map.empty,
--   -- dataEnv = Map.empty,
--   -- constructorEnv = Map.empty,
--   -- topNameEnv = Map.empty,
--   -- prefixEnv = [],
--   -- sectionEnv = [],
--   -- weakTypeEnv = IntMap.empty,
--   -- constTypeEnv = Map.empty,
--   -- defEnv = Map.empty,
--   -- lowDefEnv = Map.empty,
--   -- declEnv =
--   --   Map.fromList
--   --     [ ("malloc", ([voidPtr], voidPtr)),
--   --       ("free", ([voidPtr], voidPtr))
--   --     ],
--   -- constraintEnv = [],
--   -- suspendedConstraintEnv = Q.empty,
--   -- substEnv = IntMap.empty,
--   -- opaqueEnv = S.empty,
--   -- nopFreeSet = S.empty
--     {
--     }

runCompiler :: IO a -> IO a
runCompiler c = do
  resultOrErr <- try c
  case resultOrErr of
    Left (Error err) ->
      foldr (>>) (exitWith (ExitFailure 1)) (map outputLog err)
    Right result ->
      return result

-- runCompiler :: Compiler a -> Env -> IO a
-- runCompiler c env = do
--   resultOrErr <- try $ runStateT c env
--   case resultOrErr of
--     Left (Error err) ->
--       foldr (>>) (exitWith (ExitFailure 1)) (map outputLog err)
--     Right (result, _) ->
--       return result

--
-- global variables
--

{-# NOINLINE count #-}
count :: IORef Int
count =
  unsafePerformIO (newIORef 0)

{-# NOINLINE shouldColorize #-}
shouldColorize :: IORef Bool
shouldColorize =
  unsafePerformIO (newIORef True)

{-# NOINLINE shouldDisplayLogLocation #-}
shouldDisplayLogLocation :: IORef Bool
shouldDisplayLogLocation =
  unsafePerformIO (newIORef True)

{-# NOINLINE shouldDisplayLogLevel #-}
shouldDisplayLogLevel :: IORef Bool
shouldDisplayLogLevel =
  unsafePerformIO (newIORef True)

{-# NOINLINE shouldDisplayLogText #-}
shouldDisplayLogText :: IORef Bool
shouldDisplayLogText =
  unsafePerformIO (newIORef True)

{-# NOINLINE shouldDisplayLogFooter #-}
shouldDisplayLogFooter :: IORef Bool
shouldDisplayLogFooter =
  unsafePerformIO (newIORef True)

{-# NOINLINE shouldCancelAlloc #-}
shouldCancelAlloc :: IORef Bool
shouldCancelAlloc =
  unsafePerformIO (newIORef True)

{-# NOINLINE endOfEntry #-}
endOfEntry :: IORef String
endOfEntry =
  unsafePerformIO (newIORef "")

{-# NOINLINE topMetaNameEnv #-}
topMetaNameEnv :: IORef (Map.HashMap T.Text Ident)
topMetaNameEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE metaTermCtx #-}
metaTermCtx :: IORef SubstMetaTerm
metaTermCtx =
  unsafePerformIO (newIORef IntMap.empty)

{-# NOINLINE fileEnv #-}
fileEnv :: IORef (Map.HashMap (Path Abs File) VisitInfo)
fileEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE traceEnv #-}
traceEnv :: IORef [Path Abs File]
traceEnv =
  unsafePerformIO (newIORef [])

-- [("choice", [("left", 0), ("right", 1)]), ...]
{-# NOINLINE enumEnv #-}
enumEnv :: IORef (Map.HashMap T.Text [(T.Text, Int)])
enumEnv =
  unsafePerformIO (newIORef Map.empty)

-- [("left", ("choice", 0)), ("right", ("choice", 1)), ...]
{-# NOINLINE revEnumEnv #-}
revEnumEnv :: IORef (Map.HashMap T.Text (T.Text, Int))
revEnumEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE dataEnv #-}
dataEnv :: IORef (Map.HashMap T.Text [T.Text])
dataEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE constructorEnv #-}
constructorEnv :: IORef (Map.HashMap T.Text (Int, Int))
constructorEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE prefixEnv #-}
prefixEnv :: IORef [T.Text]
prefixEnv =
  unsafePerformIO (newIORef [])

{-# NOINLINE nsEnv #-}
nsEnv :: IORef [(T.Text, T.Text)]
nsEnv =
  unsafePerformIO (newIORef [])

{-# NOINLINE sectionEnv #-}
sectionEnv :: IORef [T.Text]
sectionEnv =
  unsafePerformIO (newIORef [])

{-# NOINLINE topNameEnv #-}
topNameEnv :: IORef (Map.HashMap T.Text Ident)
topNameEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE weakTypeEnv #-}
weakTypeEnv :: IORef (IntMap.IntMap WeakTermPlus)
weakTypeEnv =
  unsafePerformIO (newIORef IntMap.empty)

{-# NOINLINE constTypeEnv #-}
constTypeEnv :: IORef (Map.HashMap T.Text TermPlus)
constTypeEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE holeEnv #-}
holeEnv :: IORef (IntMap.IntMap (WeakTermPlus, WeakTermPlus))
holeEnv =
  unsafePerformIO (newIORef IntMap.empty)

{-# NOINLINE constraintEnv #-}
constraintEnv :: IORef [Constraint]
constraintEnv =
  unsafePerformIO (newIORef [])

{-# NOINLINE suspendedConstraintEnv #-}
suspendedConstraintEnv :: IORef SuspendedConstraintQueue
suspendedConstraintEnv =
  unsafePerformIO (newIORef Q.empty)

{-# NOINLINE substEnv #-}
substEnv :: IORef (IntMap.IntMap WeakTermPlus)
substEnv =
  unsafePerformIO (newIORef IntMap.empty)

{-# NOINLINE opaqueEnv #-}
opaqueEnv :: IORef (S.Set Ident)
opaqueEnv =
  unsafePerformIO (newIORef S.empty)

{-# NOINLINE defEnv #-}
defEnv :: IORef (Map.HashMap T.Text (IsReducible, [Ident], CompPlus))
defEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE lowDefEnv #-}
lowDefEnv :: IORef (Map.HashMap T.Text ([Ident], LowComp))
lowDefEnv =
  unsafePerformIO (newIORef Map.empty)

{-# NOINLINE declEnv #-}
declEnv :: IORef (Map.HashMap T.Text ([LowType], LowType))
declEnv =
  unsafePerformIO $
    newIORef $
      Map.fromList
        [ ("malloc", ([voidPtr], voidPtr)),
          ("free", ([voidPtr], voidPtr))
        ]

{-# NOINLINE nopFreeSet #-}
nopFreeSet :: IORef (S.Set Int)
nopFreeSet =
  unsafePerformIO (newIORef S.empty)

--
-- generating new symbols using count
--

{-# INLINE newCount #-}
newCount :: IO Int
newCount =
  atomicModifyIORef' count $ \x -> let z = x + 1 in (z, z) -- for now (i64-overflow breaks this)

{-# INLINE newIdentFromText #-}
newIdentFromText :: T.Text -> IO Ident
newIdentFromText s = do
  i <- newCount
  return $ I (s, i)

{-# INLINE newIdentFromIdent #-}
newIdentFromIdent :: Ident -> IO Ident
newIdentFromIdent x =
  newIdentFromText (asText x)

{-# INLINE newText #-}
newText :: IO T.Text
newText = do
  i <- newCount
  return $ ";" <> T.pack (show i)

{-# INLINE newAster #-}
newAster :: Hint -> IO WeakTermPlus
newAster m = do
  i <- newCount
  return (m, WeakTermAster i)

{-# INLINE newValueVarLocalWith #-}
newValueVarLocalWith :: Hint -> T.Text -> IO (Ident, ValuePlus)
newValueVarLocalWith m name = do
  x <- newIdentFromText name
  return (x, (m, ValueVarLocal x))

--
-- obtain information from the environment
--

getCurrentFilePath :: IO (Path Abs File)
getCurrentFilePath = do
  tenv <- readIORef traceEnv
  return $ head tenv

getCurrentDirPath :: IO (Path Abs Dir)
getCurrentDirPath =
  parent <$> getCurrentFilePath

getLibraryDirPath :: IO (Path Abs Dir)
getLibraryDirPath = do
  let ver = showVersion version
  relLibPath <- parseRelDir $ ".local/share/neut/" <> ver <> "/library"
  getDirPath relLibPath

getDirPath :: Path Rel Dir -> IO (Path Abs Dir)
getDirPath base = do
  homeDirPath <- getHomeDir
  let path = homeDirPath </> base
  createDirectoryIfMissing True $ toFilePath path
  return path

--
-- log
--

outputLog :: Log -> IO ()
outputLog (mpos, l, t) = do
  whenRef shouldDisplayLogLocation $
    outputLogLocation mpos
  whenRef shouldDisplayLogLevel $
    outputLogLevel l
  whenRef shouldDisplayLogText $
    outputLogText t (logLevelToPad l)
  whenRef shouldDisplayLogFooter $
    outputFooter

whenRef :: IORef Bool -> IO () -> IO ()
whenRef ref comp = do
  b <- readIORef ref
  if b
    then comp
    else return ()

outputLogLocation :: Maybe PosInfo -> IO ()
outputLogLocation mpos = do
  b <- readIORef shouldDisplayLogLocation
  case mpos of
    Just (path, loc) | b ->
      withSGR [SetConsoleIntensity BoldIntensity] $ do
        TIO.putStr $ T.pack (showPosInfo path loc)
        TIO.putStrLn ":"
    _ ->
      return ()

outputFooter :: IO ()
outputFooter = do
  eoe <- readIORef endOfEntry
  if eoe == ""
    then return ()
    else putStrLn eoe

outputPosInfo :: PosInfo -> IO ()
outputPosInfo (path, loc) =
  withSGR [SetConsoleIntensity BoldIntensity] $ do
    TIO.putStr $ T.pack (showPosInfo path loc)
    TIO.putStrLn ":"

outputLogLevel :: LogLevel -> IO ()
outputLogLevel l =
  withSGR (logLevelToSGR l) $ do
    TIO.putStr $ logLevelToText l
    TIO.putStr ": "

outputLogText :: T.Text -> IO T.Text -> IO ()
outputLogText str padComp = do
  pad <- padComp
  TIO.putStrLn $ stylizeLogText str pad

logLevelToPad :: LogLevel -> IO T.Text
logLevelToPad level = do
  b <- readIORef shouldDisplayLogLevel
  if b
    then return $ T.replicate (T.length (logLevelToText level) + 2) " "
    else return ""

stylizeLogText :: T.Text -> T.Text -> T.Text
stylizeLogText str pad = do
  let ls = T.lines str
  if null ls
    then str
    else T.intercalate "\n" $ head ls : map (pad <>) (tail ls)

withSGR :: [SGR] -> IO () -> IO ()
withSGR arg f = do
  b <- readIORef shouldColorize
  if b
    then setSGR arg >> f >> setSGR [Reset]
    else f

note :: Hint -> T.Text -> IO ()
note m str =
  outputLog $ logNote (getPosInfo m) str

note' :: T.Text -> IO ()
note' str =
  outputLog $ logNote' str

warn :: PosInfo -> T.Text -> IO ()
warn pos str =
  outputLog $ logWarning pos str

outputPass :: String -> IO ()
outputPass str =
  outputLog (Nothing, LogLevelPass, T.pack str)

outputFail :: String -> IO ()
outputFail str =
  outputLog (Nothing, LogLevelFail, T.pack str)

-- for debug
p :: String -> IO ()
p s =
  putStrLn s

p' :: (Show a) => a -> IO ()
p' s =
  putStrLn $ Pr.ppShow s
