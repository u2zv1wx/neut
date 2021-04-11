module Data.Log where

import Control.Exception.Safe
import Data.Basic
import qualified Data.Text as T
import System.Console.ANSI

data LogLevel
  = LogLevelNote
  | LogLevelWarning
  | LogLevelError
  | LogLevelCritical -- "impossible" happened
  | LogLevelPass -- for test
  | LogLevelFail -- for test
  deriving (Show, Eq)

type Log =
  (Maybe PosInfo, LogLevel, T.Text)

type ColorFlag =
  Bool

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

forgetPosInfoIfNecessary :: Bool -> Log -> Log
forgetPosInfoIfNecessary flag (_, l, t) =
  if flag
    then (Nothing, l, t)
    else (Nothing, l, t)

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
