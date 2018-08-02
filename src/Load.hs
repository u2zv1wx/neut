module Load
  ( load
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

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

load' :: [Tree] -> WithEnv ()
load' [] = return ()
load' ((_ :< TreeNode [_ :< TreeAtom "notation", from, to]):as) = do
  modify (\e -> e {notationEnv = (from, to) : notationEnv e})
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "reserve", _ :< TreeAtom s]):as) = do
  modify (\e -> e {reservedEnv = s : reservedEnv e})
  load' as
load' ((_ :< TreeNode [_ :< TreeAtom "value", _ :< TreeAtom s, tp]):as) = do
  mt <- parseType tp
  case polarizeType mt of
    Right (TypeValueType t) -> do
      modify (\e -> e {valueEnv = (s, t) : valueEnv e})
      insTEnv s (weakenValueType t)
      load' as
    Left err -> lift $ throwE err
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
        TermValue v -> do
          v' <- virtualV v
          liftIO $ putStrLn $ Pr.ppShow v'
        TermComp c -> do
          c' <- virtualC c
          liftIO $ putStrLn $ Pr.ppShow c'
      load' as
