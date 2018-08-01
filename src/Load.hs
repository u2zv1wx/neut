module Load
  ( load
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Alpha
import           Data
import           Macro
import           Parse
import           Polarize
import           Read
import           Typing
import           Virtual

import qualified Text.Show.Pretty           as Pr

load :: String -> WithEnv ()
load s = do
  astList <- strToTree s
  load' astList

load' :: [MTree] -> WithEnv ()
load' [] = return ()
load' ((Node [(Atom "notation", _), from, to], _):as) = do
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  load' as
load' ((Node [(Atom "reserve", _), (Atom s, _)], _):as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  load' as
load' ((Node [(Atom "value", _), (Atom s, _), tp], _):as) = do
  p <- parseType tp
  modify (\e -> e {valueEnv = (s, p) : valueEnv e})
  insTEnv s p
  load' as
load' (a:as) = do
  a' <- macroExpand a
  liftIO $ putStrLn $ Pr.ppShow a'
  e <- parseTerm a'
  e' <- alpha e
  check e'
  case polarize e' of
    Left err -> lift $ throwE err
    Right e''
      -- liftIO $ putStrLn $ Pr.ppShow e''
     -> do
      case e'' of
        Value v -> do
          v' <- virtualV v
          liftIO $ putStrLn $ Pr.ppShow v'
        Comp c -> do
          c' <- virtualC c
          liftIO $ putStrLn $ Pr.ppShow c'
      load' as
