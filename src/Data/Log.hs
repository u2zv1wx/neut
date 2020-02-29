{-# LANGUAGE OverloadedStrings #-}

module Data.Log
  ( LogLevel
  , outputLog
  ) where

import System.Console.ANSI

import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Data.Basic

data LogLevel
  = LogLevelHint
  | LogLevelWarning
  | LogLevelError
  | LogLevelCritical
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
  setSGR' b [SetConsoleIntensity BoldIntensity]
  TIO.putStr $ T.pack (showPosInfo path loc)
  TIO.putStrLn ":"
  setSGR' b [Reset]

outputLogLevel :: Bool -> LogLevel -> IO ()
outputLogLevel b l = do
  setSGR' b $ logLevelToSGR l
  TIO.putStr $ logLevelToText l <> ": "
  setSGR' b [Reset]

outputLogText :: T.Text -> IO ()
outputLogText = TIO.putStrLn

setSGR' :: Bool -> [SGR] -> IO ()
setSGR' False _ = return ()
setSGR' True arg = setSGR arg
