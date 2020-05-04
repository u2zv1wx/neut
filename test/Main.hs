module Main where

import Control.Exception.Safe
import Control.Monad
import Data.List
import Data.Log
import Path
import Path.IO
import System.Exit
import System.Process

main :: IO ()
main = do
  dataDir <- getDataDir
  (_, contents) <- listDir dataDir
  progList <- filterM isSourceFile contents
  result <- test $ sort progList
  if result
    then return ()
    else exitWith (ExitFailure 1)

test :: [Path Abs File] -> IO Bool
test [] = return True
test [srcPath] = test' srcPath
test (srcPath : rest) = do
  b1 <- test' srcPath
  putStr "\n"
  b2 <- test rest
  return $ b1 && b2

test' :: Path Abs File -> IO Bool
test' srcPath = do
  (binaryPath, _) <- splitExtension srcPath
  (code, out, _) <- readProcessWithExitCode "neut" ["build", toFilePath srcPath, "-o", toFilePath binaryPath] []
  result <-
    case code of
      ExitSuccess -> do
        result <- readProcess (toFilePath binaryPath) [] []
        removeFile binaryPath
        return result
      ExitFailure _ ->
        return out
  answerPath <- addExtension ".answer" binaryPath
  expectedResult <- readFile $ toFilePath answerPath
  (basename, _) <- splitExtension $ filename srcPath
  if result == expectedResult
    then do
      outputPass $ toFilePath basename
      return True
    else do
      outputFail $ toFilePath basename
      putStrLn $ prefixExpected <> stylize expectedResult
      putStrLn $ prefixFound <> stylize result
      return False

prefixExpected :: String
prefixExpected =
  "  expected: "

prefixFound :: String
prefixFound =
  "     found: "

pad :: String
pad =
  "            "

stylize :: String -> String
stylize str =
  case str of
    "" ->
      "(empty)"
    _ ->
      stylize' str

stylize' :: String -> String
stylize' str = do
  let ls = lines str
  intercalate "\n" $ head ls : map (pad ++) (tail ls)

getDataDir :: IO (Path Abs Dir)
getDataDir = do
  currentDir <- getCurrentDir
  rel <- parseRelDir "test/data"
  return $ currentDir </> rel

isSourceFile :: Path Abs File -> IO Bool
isSourceFile path =
  isSourceFile' path `catch` returnFalse

returnFalse :: PathException -> IO Bool
returnFalse _ =
  return False

isSourceFile' :: Path Abs File -> IO Bool
isSourceFile' path = do
  (_, ext) <- splitExtension path
  case ext of
    ".neut" ->
      return True
    _ ->
      return False
