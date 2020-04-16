{-# LANGUAGE OverloadedStrings #-}

module Data.Log
  ( Log
  , outputLog
  , outputLog'
  , logNote
  , logNote'
  , logWarning
  , logError
  , logCritical
  , logCritical'
  ) where

import System.Console.ANSI

import qualified Data.Text as T
import qualified Data.Text.IO as TIO

import Data.Basic

data LogLevel
  = LogLevelNote
  | LogLevelWarning
  | LogLevelError
  | LogLevelCritical -- "impossible" happened
  deriving (Show, Eq)

logLevelToText :: LogLevel -> T.Text
logLevelToText LogLevelNote = "note"
logLevelToText LogLevelWarning = "warning"
logLevelToText LogLevelError = "error"
logLevelToText LogLevelCritical = "critical"

logLevelToSGR :: LogLevel -> [SGR]
logLevelToSGR LogLevelNote =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Blue]
logLevelToSGR LogLevelWarning =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Yellow]
logLevelToSGR LogLevelError =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
logLevelToSGR LogLevelCritical =
  [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]

type Log = (Maybe PosInfo, LogLevel, T.Text)

type ColorFlag = Bool

outputLog :: ColorFlag -> String -> Log -> IO ()
outputLog b eoe (Nothing, l, t) = do
  outputLogLevel b l
  outputLogText t
  outputFooter eoe
outputLog b eoe (Just pos, l, t) = do
  outputPosInfo b pos
  outputLogLevel b l
  outputLogText t
  outputFooter eoe

outputLog' :: ColorFlag -> Log -> IO ()
outputLog' b (Nothing, l, t) = do
  outputLogLevel b l
  TIO.putStr t
outputLog' b (Just pos, l, t) = do
  outputPosInfo b pos
  outputLogLevel b l
  TIO.putStr t

outputFooter :: String -> IO ()
outputFooter "" = return ()
outputFooter eoe = putStrLn eoe

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

logNote :: PosInfo -> T.Text -> Log
logNote pos text = (Just pos, LogLevelNote, text)

logNote' :: T.Text -> Log
logNote' text = (Nothing, LogLevelNote, text)

logWarning :: PosInfo -> T.Text -> Log
logWarning pos text = (Just pos, LogLevelWarning, text)

logError :: PosInfo -> T.Text -> Log
logError pos text = (Just pos, LogLevelError, text)

logCritical :: PosInfo -> T.Text -> Log
logCritical pos text = (Just pos, LogLevelCritical, text)

logCritical' :: T.Text -> Log
logCritical' text = (Nothing, LogLevelCritical, text)
