module Main where

import Control.Exception.Safe
import Control.Monad
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
  putStrLn "source path:"
  currentDir <- getCurrentDir
  srcPath' <- stripProperPrefix currentDir srcPath
  putStrLn $ toFilePath srcPath'
  callProcess "neut" ["build", toFilePath srcPath, "-o", toFilePath binaryPath]
  result <- readProcess (toFilePath binaryPath) [] []
  expectedResult <- readFile $ toFilePath answerPath
  if result == expectedResult
    then do
      putStrLn "passed."
      return True
    else do
      putStrLn "mismatch."
      return False

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
