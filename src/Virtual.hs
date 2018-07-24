module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data

virtualV :: MV -> WithEnv Operand
virtualV (VVar s, _) = return $ Register s
virtualV (VConst s, _) = return $ ConstCell (CellAtom s)
virtualV (VConsApp v1 v2, _) = do
  o1 <- virtualV v1
  o2 <- virtualV v2
  case (o1, o2) of
    (ConstCell cell1, ConstCell cell2) ->
      return $ ConstCell (CellCons cell1 cell2)
    (ConstCell cell1, Register regName) ->
      return $ ConstCell (CellCons cell1 (CellReg regName))
    _ -> lift $ throwE $ "virtualV : " ++ show v1 ++ "\n" ++ show v2
virtualV (VThunk c, _) = do
  let fvs = freeVarN c
  asm <- virtualC c
  return $ Alloc asm fvs
virtualV (VAsc v _, _) = virtualV v

virtualC :: MC -> WithEnv Operation
virtualC (CLam _ e, _) = virtualC e
virtualC (CApp e v, i) = do
  let (fun, args) = funAndArgs (CApp e v, i)
  let formalArgs = getArgs fun
  argOperands <- mapM virtualV args
  funOperation <- virtualC fun
  return $
    foldr (\(i, argOp) rest -> Let i argOp rest) funOperation $
    zip formalArgs argOperands
virtualC (CRet v, _) = do
  asm <- virtualV v
  return $ Ans asm
virtualC (CBind (S s _) c1 c2, _) = do
  operation1 <- virtualC c1
  operation2 <- virtualC c2
  case operation1 of
    Ans operand -> return $ Let s operand operation2
    e           -> lift $ throwE $ "CBind: " ++ show e
virtualC (CUnthunk v, _) = do
  operand <- virtualV v
  case operand of
    Register s -> return $ Jump s
    Alloc op _ -> return op
virtualC (CSend s c, _) = undefined
virtualC (CRecv s c, _) = undefined
virtualC (CDispatch c1 c2, _) = undefined
virtualC (CColeft c, _) = undefined
virtualC (CCoright c, _) = undefined
virtualC (CMu s c, _) = undefined
virtualC (CCase c vcs, _) = undefined
virtualC (CAsc c _, _) = virtualC c

funAndArgs :: MC -> (MC, [MV])
funAndArgs (CApp e v, _) = do
  let (fun, args) = funAndArgs e
  (fun, v : args)
funAndArgs e = (e, [])

getArgs :: MC -> [String]
getArgs (CLam (S s _) e, _) = s : getArgs e
getArgs _                   = []

freeVarP :: MV -> [String]
freeVarP (VVar s, _)         = [s]
freeVarP (VConst _, _)       = []
freeVarP (VConsApp v1 v2, _) = freeVarP v1 ++ freeVarP v2
freeVarP (VThunk e, _)       = freeVarN e
freeVarP (VAsc e t, _)       = freeVarP e

freeVarN :: MC -> [String]
freeVarN (CLam (S s t) e, _) = filter (/= s) (freeVarN e)
freeVarN (CApp e v, _) = freeVarN e ++ freeVarP v
freeVarN (CRet v, _) = freeVarP v
freeVarN (CBind (S s t) e1 e2, _) = freeVarN e1 ++ filter (/= s) (freeVarN e2)
freeVarN (CUnthunk v, _) = freeVarP v
freeVarN (CSend (S s t) e, _) = s : freeVarN e
freeVarN (CRecv (S s t) e, _) = filter (/= s) (freeVarN e)
freeVarN (CDispatch e1 e2, _) = freeVarN e1 ++ freeVarN e2
freeVarN (CColeft e, _) = freeVarN e
freeVarN (CCoright e, _) = freeVarN e
freeVarN (CMu (S s t) e, _) = filter (/= s) (freeVarN e)
freeVarN (CCase e ves, _) = do
  let efs = freeVarN e
  vefss <-
    forM ves $ \(pat, body) -> do
      bound <- freeVarP pat
      fs <- freeVarN body
      return $ filter (`notElem` bound) fs
  efs ++ vefss
freeVarN (CAsc e t, _) = freeVarN e
