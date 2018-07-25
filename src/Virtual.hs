module Virtual where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data

import qualified Text.Show.Pretty           as Pr

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
  let fvs = varN c
  asm <- virtualC c
  return $ Alloc asm fvs
virtualV (VAsc v _, _) = virtualV v

virtualC :: MC -> WithEnv Operation
virtualC (CLam _ e, _) = virtualC e
virtualC (CApp e@(_, i) v, _) = do
  mt <- lookupTEnv i
  case mt of
    Nothing -> lift $ throwE "ERROR<virtualC>"
    Just (TForall (SHole symbol _) _) -> undefined
    Just (TForall (S symbol _) _) -> do
      argAsm <- virtualV v
      cont <- virtualC e
      return $ Let symbol argAsm cont
virtualC (CRet v, _) = do
  asm <- virtualV v
  return $ Ans asm
virtualC (CBind (S s _) c1 c2, _) = do
  operation1 <- virtualC c1
  operation2 <- virtualC c2
  return $ traceLet s operation1 operation2
virtualC (CUnthunk v, _) = do
  operand <- virtualV v
  case operand of
    Register s -> return $ Jump s
    Alloc op _ -> return op
    _          -> lift $ throwE "virtualC.CUnthunk"
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

traceLet :: String -> Operation -> Operation -> Operation
traceLet s (Ans o) cont       = Let s o cont
traceLet s (Jump addr) cont   = LetCall s addr cont
traceLet s (Let k o1 o2) cont = Let k o1 (traceLet s o2 cont)

getArgs :: MC -> [String]
getArgs (CLam (S s _) e, _) = s : getArgs e
getArgs _                   = []

varP :: MV -> [String]
varP (VVar s, _)         = [s]
varP (VConst _, _)       = []
varP (VConsApp v1 v2, _) = varP v1 ++ varP v2
varP (VThunk e, _)       = varN e
varP (VAsc e t, _)       = varP e

varN :: MC -> [String]
varN (CLam (S s t) e, _) = filter (/= s) $ varN e
varN (CApp e v, _) = varN e ++ varP v
varN (CRet v, _) = varP v
varN (CBind (S s t) e1 e2, _) = varN e1 ++ filter (/= s) (varN e2)
varN (CUnthunk v, _) = varP v
varN (CSend (S s t) e, _) = s : varN e
varN (CRecv (S s t) e, _) = filter (/= s) (varN e)
varN (CDispatch e1 e2, _) = varN e1 ++ varN e2
varN (CColeft e, _) = varN e
varN (CCoright e, _) = varN e
varN (CMu (S s t) e, _) = filter (/= s) (varN e)
varN (CCase e ves, _) = do
  let efs = varN e
  vefss <-
    forM ves $ \(pat, body) -> do
      bound <- varP pat
      fs <- varN body
      return $ filter (`notElem` bound) fs
  efs ++ vefss
varN (CAsc e t, _) = varN e
