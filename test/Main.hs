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
  resultList <- forM (sort progList) test
  if or resultList
    then return ()
    else exitWith (ExitFailure 1)

test :: Path Abs File -> IO Bool
test srcPath = do
  (binaryPath, _) <- splitExtension srcPath
  answerPath <- addExtension ".answer" binaryPath
  callProcess "neut" ["build", toFilePath srcPath, "-o", toFilePath binaryPath]
  result <- readProcess (toFilePath binaryPath) [] []
  removeFile binaryPath
  expectedResult <- readFile $ toFilePath answerPath
  (basename, _) <- splitExtension $ filename srcPath
  if result == expectedResult
    then do
      outputPass $ toFilePath basename
      return True
    else do
      outputFail $ toFilePath basename
      putStrLn $ "  expected: " <> stylize expectedResult
      putStrLn $ "     found: " <> stylize result
      return False

stylize :: String -> String
stylize str =
  case str of
    "" ->
      "(empty)"
    _ ->
      str

getDataDir :: IO (Path Abs Dir)
getDataDir = do
  currentDir <- getCurrentDir
  rel <- parseRelDir "test/data"
  return $ currentDir </> rel

isSourceFile :: Path Abs File -> IO Bool
isSourceFile path =
  catch (isSourceFile' path) (\(_ :: PathException) -> return False)

isSourceFile' :: Path Abs File -> IO Bool
isSourceFile' path = do
  (_, ext) <- splitExtension path
  case ext of
    ".neut" ->
      return True
    _ ->
      return False
