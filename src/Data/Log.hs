{-# LANGUAGE OverloadedStrings #-}

module Data.Log
  ( Log
  , outputLog
  , logError
  , logError'
  , logCritical
  , logCritical'
  ) where

import System.Console.ANSI

import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Data.Basic

data LogLevel
  = LogLevelHint
  | LogLevelWarning
  | LogLevelError
  | LogLevelCritical -- "impossible" happened
  deriving (Show)

logLevelToText :: LogLevel -> T.Text
logLevelToText LogLevelHint = "hint"
logLevelToText LogLevelWarning = "warning"
logLevelToText LogLevelError = "error"
logLevelToText LogLevelCritical = "critical"

logLevelToSGR :: LogLevel -> [SGR]
logLevelToSGR LogLevelHint =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Blue]
logLevelToSGR LogLevelWarning =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Yellow]
logLevelToSGR LogLevelError =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
logLevelToSGR LogLevelCritical =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]

type Log = (Maybe PosInfo, LogLevel, T.Text)

type ColorFlag = Bool

outputLog :: ColorFlag -> Log -> IO ()
outputLog b (Nothing, l, t) = do
  outputLogLevel b l
  outputLogText t
outputLog b (Just pos, l, t) = do
  outputPosInfo b pos
  outputLogLevel b l
  outputLogText t

outputPosInfo :: Bool -> PosInfo -> IO ()
outputPosInfo b (path, loc) = do
  withSGR b [SetConsoleIntensity BoldIntensity] $ do
    TIO.putStr $ T.pack (showPosInfo path loc)
    TIO.putStrLn ":"

outputLogLevel :: Bool -> LogLevel -> IO ()
outputLogLevel b l = do
  withSGR b (logLevelToSGR l) $ do
    TIO.putStr $ logLevelToText l
    TIO.putStr ": "

outputLogText :: T.Text -> IO ()
outputLogText = TIO.putStrLn

withSGR :: Bool -> [SGR] -> IO () -> IO ()
withSGR False _ f = f
withSGR True arg f = setSGR arg >> f >> setSGR [Reset]

logError :: Maybe PosInfo -> T.Text -> Log
logError mpos text = (mpos, LogLevelError, text)

logError' :: T.Text -> Log
logError' text = logError Nothing text

logCritical :: Maybe PosInfo -> T.Text -> Log
logCritical mpos text = (mpos, LogLevelCritical, text)

logCritical' :: T.Text -> Log
logCritical' text = logCritical Nothing text