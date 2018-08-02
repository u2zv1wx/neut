module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

virtualV :: Value -> WithEnv Operand
virtualV (ValueVar s) = return $ Register s
virtualV (ValueConst s) = return $ ConstCell (CellAtom s)
virtualV (ValueThunk c) = do
  let fvs = varN c
  asm <- virtualC c
  return $ Alloc asm fvs

virtualC :: Comp -> WithEnv Operation
virtualC (CompLam _ e) = undefined -- return "closure"-like object
virtualC (CompApp e v) = do
  e' <- virtualC e
  -- deconstruct e' and get "closure" or constant
  undefined
virtualC (CompRet v) = do
  asm <- virtualV v
  return $ Ans asm
virtualC (CompBind s c1 c2) = do
  operation1 <- virtualC c1
  operation2 <- virtualC c2
  return $ traceLet s operation1 operation2
virtualC (CompUnthunk v) = do
  operand <- virtualV v
  case operand of
    Register s -> return $ Jump s
    Alloc op _ -> return op
    _          -> lift $ throwE "virtualC.CUnthunk"
virtualC (CompMu s c) = undefined
virtualC (CompCase c vcs) = undefined

funAndArgs :: Comp -> (Comp, [Value])
funAndArgs (CompApp e v) = do
  let (fun, args) = funAndArgs e
  (fun, v : args)
funAndArgs e = (e, [])

traceLet :: String -> Operation -> Operation -> Operation
traceLet s (Ans o) cont       = Let s o cont
traceLet s (Jump addr) cont   = LetCall s addr cont
traceLet s (Let k o1 o2) cont = Let k o1 (traceLet s o2 cont)

getArgs :: Comp -> [String]
getArgs (CompLam s e) = s : getArgs e
getArgs _             = []

varP :: Value -> [String]
varP (ValueVar s)   = [s]
varP (ValueConst _) = []
varP (ValueThunk e) = varN e

varN :: Comp -> [String]
varN (CompLam s e) = filter (/= s) $ varN e
varN (CompApp e v) = varN e ++ varP v
varN (CompRet v) = varP v
varN (CompBind s e1 e2) = varN e1 ++ filter (/= s) (varN e2)
varN (CompUnthunk v) = varP v
varN (CompMu s e) = filter (/= s) (varN e)
varN (CompCase e ves) = do
  let efs = varP e
  vefss <-
    forM ves $ \(pat, body) -> do
      bound <- varPat pat
      fs <- varN body
      return $ filter (`notElem` bound) fs
  efs ++ vefss

varPat :: Pat -> [String]
varPat (_ :< PatVar s)     = [s]
varPat (_ :< PatConst _)   = []
varPat (_ :< PatApp p1 p2) = varPat p1 ++ varPat p2
