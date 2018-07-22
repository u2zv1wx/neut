module Main where

import           Control.Monad
import           Control.Monad.State
import           Debug.Trace

import qualified Text.Show.Pretty    as Pr

import           Data
import           Macro
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
  item <- runWithEnv (foo content) initialEnv
  case item of
    Left err -> putStrLn err
    Right (astList, env) -> do
      putStrLn $ Pr.ppShow (astList, env)
  -- evalWithEnv (readExpr "lisp" content) initialEnv
  -- p <- liftIO $ runWithEnv (readExpr "lisp" content) initialEnv
  -- case p of
  --   Left err -> putStrLn err
  --   Right (result, _) -> putStrLn $ Pr.ppShow result

foo :: String -> WithEnv [Expr]
foo input = do
  astList <- strToTree input
  ts <- loadMacroDef astList
  ts' <- mapM macroExpand ts
  liftIO $ putStrLn $ Pr.ppShow ts'
  parse ts'
