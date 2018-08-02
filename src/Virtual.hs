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
virtualV (Value (_ :< ValueVar s)) = return $ Register s
virtualV (Value (_ :< ValueConst s)) = return $ ConstCell (CellAtom s)
virtualV (Value (_ :< ValueThunk c)) = do
  let fvs = varN c
  asm <- virtualC c
  return $ Alloc asm fvs

virtualC :: Comp -> WithEnv Operation
virtualC (Comp (_ :< CompLam _ e)) = undefined -- return "closure"-like object
virtualC (Comp (_ :< CompApp e@(Meta {ident = i} :< _) v)) = do
  e' <- virtualC (Comp e)
  -- deconstruct e' and get "closure" or constant
  undefined
virtualC (Comp (_ :< CompRet v)) = do
  asm <- virtualV v
  return $ Ans asm
virtualC (Comp (_ :< CompBind s c1 c2)) = do
  operation1 <- virtualC (Comp c1)
  operation2 <- virtualC (Comp c2)
  return $ traceLet s operation1 operation2
virtualC (Comp (_ :< CompUnthunk v)) = do
  operand <- virtualV v
  case operand of
    Register s -> return $ Jump s
    Alloc op _ -> return op
    _          -> lift $ throwE "virtualC.CUnthunk"
virtualC (Comp (_ :< CompMu s c)) = undefined
virtualC (Comp (_ :< CompCase c vcs)) = undefined

funAndArgs :: Comp -> (Comp, [Value])
funAndArgs (Comp (_ :< CompApp e v)) = do
  let (fun, args) = funAndArgs (Comp e)
  (fun, v : args)
funAndArgs e = (e, [])

traceLet :: String -> Operation -> Operation -> Operation
traceLet s (Ans o) cont       = Let s o cont
traceLet s (Jump addr) cont   = LetCall s addr cont
traceLet s (Let k o1 o2) cont = Let k o1 (traceLet s o2 cont)

getArgs :: Comp -> [String]
getArgs (Comp (_ :< CompLam s e)) = s : getArgs (Comp e)
getArgs _                         = []

varP :: Value -> [String]
varP (Value (_ :< ValueVar s))   = [s]
varP (Value (_ :< ValueConst _)) = []
varP (Value (_ :< ValueThunk e)) = varN e

varN :: Comp -> [String]
varN (Comp (_ :< CompLam s e)) = filter (/= s) $ varN (Comp e)
varN (Comp (_ :< CompApp e v)) = varN (Comp e) ++ varP v
varN (Comp (_ :< CompRet v)) = varP v
varN (Comp (_ :< CompBind s e1 e2)) =
  varN (Comp e1) ++ filter (/= s) (varN (Comp e2))
varN (Comp (_ :< CompUnthunk v)) = varP v
varN (Comp (_ :< CompMu s e)) = filter (/= s) (varN (Comp e))
varN (Comp (_ :< CompCase e ves)) = do
  let efs = varP e
  vefss <-
    forM ves $ \(pat, body) -> do
      bound <- varPat pat
      fs <- varN (Comp body)
      return $ filter (`notElem` bound) fs
  efs ++ vefss

varPat :: Pat -> [String]
varPat (_ :< PatVar s)     = [s]
varPat (_ :< PatConst _)   = []
varPat (_ :< PatApp p1 p2) = varPat p1 ++ varPat p2
