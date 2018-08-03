module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

virtualV :: Value -> WithEnv Data
virtualV (ValueVar s) = return $ DataPointer s
virtualV (ValueConst s) = return $ DataCell s []
virtualV (ValueNodeApp s vs) = do
  vs' <- mapM virtualV vs
  return $ DataCell s vs'
virtualV (ValueThunk c) = do
  asm <- virtualC c
  return $ DataThunk asm

virtualC :: Comp -> WithEnv Code
virtualC (CompLam i e) = do
  e' <- virtualC e
  return $ CodeFragment i e'
virtualC (CompApp e v) = do
  me' <- virtualC e
  case me' of
    CodeFragment i e' -> do
      v' <- virtualV v
      return $ CodeLet i (CodeAllocate v') e'
    CodeJump i args -> do
      v' <- virtualV v
      return $ CodeJump i (v' : args)
    t -> lift $ throwE $ "virtualC.CompApp. Note:\n " ++ Pr.ppShow t
virtualC (CompRet v) = do
  asm <- virtualV v
  return $ CodeAllocate asm
virtualC (CompBind s c1 c2) = do
  operation1 <- virtualC c1
  operation2 <- virtualC c2
  return $ traceLet s operation1 operation2
virtualC (CompUnthunk v) = do
  operand <- virtualV v
  case operand of
    DataPointer s -> return $ CodeJump s []
    DataThunk op  -> return op
    _             -> lift $ throwE "virtualC.CUnthunk"
virtualC (CompMu s c) = undefined
virtualC (CompCase c vcs) = undefined

funAndArgs :: Comp -> (Comp, [Value])
funAndArgs (CompApp e v) = do
  let (fun, args) = funAndArgs e
  (fun, v : args)
funAndArgs e = (e, [])

traceLet :: String -> Code -> Code -> Code
traceLet s (CodeAllocate o) cont = CodeLet s (CodeAllocate o) cont
traceLet s (CodeJump addr args) cont = CodeLet s (CodeJump addr args) cont
traceLet s (CodeLet k o1 o2) cont = CodeLet k o1 (traceLet s o2 cont)
traceLet s c1 c2 =
  error $
  "traceLet. s:\n" ++
  Pr.ppShow s ++ "\nc1:\n" ++ Pr.ppShow c1 ++ "\nc2:\n" ++ Pr.ppShow c2

getArgs :: Comp -> [String]
getArgs (CompLam s e) = s : getArgs e
getArgs _             = []
