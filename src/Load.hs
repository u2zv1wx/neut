module Load
  ( load
  ) where

import           Control.Monad.State

import           Alpha
import           Data
import           Macro
import           Parse
import           Read
import           Typing

import qualified Text.Show.Pretty    as Pr

load :: String -> WithEnv ()
load s = do
  astList <- strToTree s
  load' astList

load' :: [Tree] -> WithEnv ()
load' [] = return ()
load' (Node [Atom "notation", from, to]:as) = do
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  load' as
load' (Node [Atom "reserve", Atom s]:as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  load' as
load' (Node [Atom "value", Atom s, tp]:as) = do
  p <- parseType tp
  modify (\e -> e {valueEnv = S s p : valueEnv e})
  load' as
load' (a:as) = do
  a' <- macroExpand a
  liftIO $ putStrLn $ Pr.ppShow a'
  e <- parseExpr a'
  e' <- alpha e
  check e'
  liftIO $ putStrLn $ Pr.ppShow e'
  load' as
