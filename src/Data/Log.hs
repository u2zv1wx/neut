module Data.Log
  ( Log,
    Error (Error),
    outputLog,
    outputLog',
    outputPass,
    outputFail,
    logNote,
    logNote',
    logWarning,
    logError,
    logError',
    logCritical,
    logCritical',
    raiseError,
    raiseError',
    raiseCritical,
    raiseCritical',
    raiseSyntaxError,
  )
where

import Control.Exception.Safe
import Data.Hint
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Console.ANSI

data LogLevel
  = LogLevelNote
  | LogLevelPass -- for test
  | LogLevelWarning
  | LogLevelError
  | LogLevelFail -- for test
  | LogLevelCritical -- "impossible" happened
  deriving (Show, Eq)

newtype Error
  = Error [Log]
  deriving (Show)

instance Exception Error

logLevelToText :: LogLevel -> T.Text
logLevelToText level =
  case level of
    LogLevelNote ->
      "note"
    LogLevelPass ->
      "pass"
    LogLevelWarning ->
      "warning"
    LogLevelError ->
      "error"
    LogLevelFail ->
      "fail"
    LogLevelCritical ->
      "critical"

logLevelToSGR :: LogLevel -> [SGR]
logLevelToSGR level =
  case level of
    LogLevelNote ->
      [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Blue]
    LogLevelPass ->
      [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Blue]
    LogLevelWarning ->
      [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Yellow]
    LogLevelError ->
      [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
    LogLevelFail ->
      [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
    LogLevelCritical ->
      [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]

type Log =
  (Maybe PosInfo, LogLevel, T.Text)

type ColorFlag =
  Bool

outputLog :: ColorFlag -> String -> Log -> IO ()
outputLog b eoe (mpos, l, t) = do
  case mpos of
    Nothing ->
      return ()
    Just pos ->
      outputPosInfo b pos
  outputLogLevel b l
  outputLogText t
  outputFooter eoe

outputLog' :: ColorFlag -> Log -> IO ()
outputLog' b (mpos, l, t) = do
  case mpos of
    Nothing ->
      return ()
    Just pos ->
      outputPosInfo b pos
  outputLogLevel b l
  TIO.putStr t

outputPass :: String -> IO ()
outputPass str = do
  outputLog' True (Nothing, LogLevelPass, T.pack str)
  putStr "\n"

outputFail :: String -> IO ()
outputFail str = do
  outputLog' True (Nothing, LogLevelFail, T.pack str)
  putStr "\n"

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

outputLogText :: T.Text -> IO ()
outputLogText =
  TIO.putStrLn

withSGR :: Bool -> [SGR] -> IO () -> IO ()
withSGR b arg f =
  if b
    then setSGR arg >> f >> setSGR [Reset]
    else f

logNote :: PosInfo -> T.Text -> Log
logNote pos text =
  (Just pos, LogLevelNote, text)

logNote' :: T.Text -> Log
logNote' text =
  (Nothing, LogLevelNote, text)

logWarning :: PosInfo -> T.Text -> Log
logWarning pos text =
  (Just pos, LogLevelWarning, text)

logError :: PosInfo -> T.Text -> Log
logError pos text =
  (Just pos, LogLevelError, text)

logError' :: T.Text -> Log
logError' text =
  (Nothing, LogLevelError, text)

logCritical :: PosInfo -> T.Text -> Log
logCritical pos text =
  (Just pos, LogLevelCritical, text)

logCritical' :: T.Text -> Log
logCritical' text =
  (Nothing, LogLevelCritical, text)

raiseError :: (MonadThrow m) => Hint -> T.Text -> m a
raiseError m text =
  throw $ Error [logError (getPosInfo m) text]

raiseError' :: (MonadThrow m) => T.Text -> m a
raiseError' text =
  throw $ Error [logError' text]

raiseCritical :: (MonadThrow m) => Hint -> T.Text -> m a
raiseCritical m text =
  throw $ Error [logCritical (getPosInfo m) text]

raiseCritical' :: (MonadThrow m) => T.Text -> m a
raiseCritical' text =
  throw $ Error [logCritical' text]

raiseSyntaxError :: (MonadThrow m) => Hint -> T.Text -> m a
raiseSyntaxError m form =
  raiseError m $ "couldn't match the input with the expected form: " <> form
