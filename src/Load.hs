module Load
  ( load
  ) where

import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data
import           Infer
import           Macro
import           Parse
import           Polarize
import           Read
import           Rename
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
  t <- polarizeType mt
  case t of
    TypeValueType t -> do
      modify (\e -> e {valueEnv = (s, t) : valueEnv e})
      insWTEnv s (weakenValueType t)
      load' as
    _ ->
      lift $
      throwE $ "the polarity of value type " ++ show s ++ " must be positive"
load' (a:as) = do
  a' <- macroExpand a
  liftIO $ putStrLn $ Pr.ppShow a'
  e <- parseTerm a'
  liftIO $ putStrLn $ Pr.ppShow e
  e' <- rename e
  check e'
  env <- get
  let wtenv = weakTypeEnv env
  tenv <- polarizeTypeEnv wtenv
  modify (\e -> e {typeEnv = tenv})
  case polarize e' of
    Left err -> lift $ throwE err
    Right e'' -> do
      case e'' of
        TermValue v -> do
          liftIO $ putStrLn $ Pr.ppShow v
          v' <- virtualV v
          liftIO $ putStrLn $ Pr.ppShow v'
          liftIO $ putStrLn "the type of main term must be negative"
        TermComp c -> do
          liftIO $ putStrLn $ Pr.ppShow c
          c' <- virtualC c
          liftIO $ putStrLn $ Pr.ppShow c'
          i <- newNameWith "main"
          insCodeEnv i c'
      load' as
