module Main where

import           Control.Monad
import           Control.Monad.State
import           Debug.Trace

import qualified Text.Show.Pretty    as Pr

import           Data
import           Parse
import           Read

import           System.Environment

main :: IO ()
main = do
  pathList <- getArgs
  forM_ pathList printFile

printFile :: String -> IO ()
printFile path = do
  content <- readFile path
  evalWithEnv (strToTree content) initialEnv
  -- evalWithEnv (readExpr "lisp" content) initialEnv
  -- p <- liftIO $ runWithEnv (readExpr "lisp" content) initialEnv
  -- case p of
  --   Left err -> putStrLn err
  --   Right (result, _) -> putStrLn $ Pr.ppShow result
