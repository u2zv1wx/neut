module Main where

import           Control.Monad
import           Control.Monad.State
import           Debug.Trace

import qualified Text.Show.Pretty    as Pr

import           Data
import           Load

import           System.Environment

main :: IO ()
main = do
  pathList <- getArgs
  forM_ pathList printFile

printFile :: String -> IO ()
printFile path = do
  content <- readFile path
  item <- runWithEnv (load content) initialEnv
  case item of
    Left err             -> putStrLn err
    Right (astList, env) -> return ()
      --putStrLn $ Pr.ppShow (astList, env)
