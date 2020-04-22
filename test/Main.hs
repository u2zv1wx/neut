module Main where

import Control.Exception.Safe
import Control.Monad
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
  resultList <- forM progList test
  if or resultList
    then return ()
    else exitWith (ExitFailure 1)

test :: Path Abs File -> IO Bool
test srcPath = do
  (binaryPath, _) <- splitExtension srcPath
  answerPath <- addExtension ".answer" binaryPath
  dataDir <- getDataDir
  srcPath' <- stripProperPrefix dataDir srcPath
  callProcess "neut" ["build", toFilePath srcPath, "-o", toFilePath binaryPath]
  result <- readProcess (toFilePath binaryPath) [] []
  expectedResult <- readFile $ toFilePath answerPath
  if result == expectedResult
    then do
      outputPass $ toFilePath srcPath'
      return True
    else do
      outputFail $ toFilePath srcPath'
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
