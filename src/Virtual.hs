module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data

virtualV :: V -> WithEnv Operand
virtualV (VVar s) = return $ Register s
virtualV (VConst s) = undefined
virtualV (VConsApp v1 v2) = undefined
virtualV (VThunk c) = do
  let fvs = freeVarN c
  asm <- virtualC c
  return $ Alloc asm fvs
virtualV (VAsc v _) = virtualV v

virtualC :: C -> WithEnv Operation
virtualC (CLam _ e) = virtualC e
virtualC (CApp e v) = do
  let (fun, args) = funAndArgs (CApp e v)
  let formalArgs = getArgs fun
  argOperands <- mapM virtualV args
  funOperation <- virtualC fun
  return $
    foldr (\(i, argOp) rest -> Let i argOp rest) funOperation $
    zip formalArgs argOperands
virtualC (CRet v) = do
  asm <- virtualV v
  return $ Ans asm
virtualC (CBind (S s _) c1 c2) = do
  operation1 <- virtualC c1
  operation2 <- virtualC c2
  case operation1 of
    Ans operand -> return $ Let s operand operation2
    e           -> lift $ throwE $ "CBind: " ++ show e
virtualC (CUnthunk v) = do
  operand <- virtualV v
  case operand of
    Register s -> return $ Jump s
    Alloc op _ -> return op -- (unthunk (thunk e))
virtualC (CSend s c) = undefined
virtualC (CRecv s c) = undefined
virtualC (CDispatch c1 c2) = undefined
virtualC (CColeft c) = undefined
virtualC (CCoright c) = undefined
virtualC (CMu s c) = undefined
virtualC (CCase c vcs) = undefined
virtualC (CAsc c _) = virtualC c

funAndArgs :: C -> (C, [V])
funAndArgs (CApp e v) = do
  let (fun, args) = funAndArgs e
  (fun, v : args)
funAndArgs e = (e, [])

getArgs :: C -> [String]
getArgs (CLam (S s _) e) = s : getArgs e
getArgs _                = []

freeVarP :: V -> [String]
freeVarP (VVar s)         = [s]
freeVarP (VConst _)       = []
freeVarP (VConsApp v1 v2) = freeVarP v1 ++ freeVarP v2
freeVarP (VThunk e)       = freeVarN e
freeVarP (VAsc e t)       = freeVarP e

freeVarN :: C -> [String]
freeVarN (CLam (S s t) e) = filter (/= s) (freeVarN e)
freeVarN (CApp e v) = freeVarN e ++ freeVarP v
freeVarN (CRet v) = freeVarP v
freeVarN (CBind (S s t) e1 e2) = freeVarN e1 ++ filter (/= s) (freeVarN e2)
freeVarN (CUnthunk v) = freeVarP v
freeVarN (CSend (S s t) e) = s : freeVarN e
freeVarN (CRecv (S s t) e) = filter (/= s) (freeVarN e)
freeVarN (CDispatch e1 e2) = freeVarN e1 ++ freeVarN e2
freeVarN (CColeft e) = freeVarN e
freeVarN (CCoright e) = freeVarN e
freeVarN (CMu (S s t) e) = filter (/= s) (freeVarN e)
freeVarN (CCase e ves) = do
  let efs = freeVarN e
  vefss <-
    forM ves $ \(pat, body) -> do
      bound <- freeVarP pat
      fs <- freeVarN body
      return $ filter (`notElem` bound) fs
  efs ++ vefss
freeVarN (CAsc e t) = freeVarN e
