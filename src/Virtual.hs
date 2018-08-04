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
virtualV (Value (i :< ValueVar s)) = return $ DataPointer s
virtualV (Value (i :< ValueConst s)) = return $ DataCell s []
virtualV (Value (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (virtualV . Value) vs
  return $ DataCell s vs'
virtualV (Value (i :< ValueThunk c)) = do
  asm <- virtualC c
  return $ DataThunk asm

virtualC :: Comp -> WithEnv Code
virtualC (Comp (i :< CompLam x e)) = do
  e' <- virtualC (Comp e)
  return $ CodeFragment x e'
virtualC (Comp (i :< CompApp e v)) = do
  me' <- virtualC (Comp e)
  case me' of
    CodeFragment i e' -> do
      v' <- virtualV v
      return $ CodeLet i (CodeAllocate v') e'
    CodeJump i args -> do
      v' <- virtualV v
      return $ CodeJump i (v' : args)
    t -> lift $ throwE $ "virtualC.CompApp. Note:\n " ++ Pr.ppShow t
virtualC (Comp (i :< CompRet v)) = do
  asm <- virtualV v
  return $ CodeAllocate asm
virtualC (Comp (i :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  return $ traceLet s operation1 operation2
virtualC (Comp (i :< CompUnthunk v)) = do
  operand <- virtualV v
  case operand of
    DataPointer s -> return $ CodeJump s []
    DataThunk op  -> return op
    _             -> lift $ throwE "virtualC.CUnthunk"
virtualC (Comp (i :< CompMu s c)) = undefined
virtualC (Comp (i :< CompCase c vcs)) = undefined

traceLet :: String -> Code -> Code -> Code
traceLet s (CodeAllocate o) cont = CodeLet s (CodeAllocate o) cont
traceLet s (CodeJump addr args) cont = CodeLet s (CodeJump addr args) cont
traceLet s (CodeLet k o1 o2) cont = CodeLet k o1 (traceLet s o2 cont)
traceLet s c1 c2 =
  error $
  "traceLet. s:\n" ++
  Pr.ppShow s ++ "\nc1:\n" ++ Pr.ppShow c1 ++ "\nc2:\n" ++ Pr.ppShow c2
