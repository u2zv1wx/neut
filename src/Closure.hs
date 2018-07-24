module Closure where

import           Control.Monad
import           Control.Monad.State
import           Data

cls :: Term -> WithEnv Term
cls (Var s) = return $ Var s
cls (Const s) = return $ Const s
cls (Lam (S s t) e) = do
  e' <- cls e
  return $ Lam (S s t) e'
cls (App e v) = do
  e' <- cls e
  v' <- cls v
  return $ App e' v'
cls (ConsApp v1 v2) = do
  v1' <- cls v1
  v2' <- cls v2
  return $ ConsApp v1' v2'
cls (Ret v) = do
  v' <- cls v
  return $ Ret v'
cls (Bind (S s t) e1 e2) = do
  e1' <- cls e1
  e2' <- cls e2
  return $ Bind (S s t) e1' e2'
cls (Thunk e) = do
  e' <- cls e
  let fv = freeVar e'
  i <- newNameWith "thunk"
  let tmp = (i, fv, e')
  modify (\e -> e {clsEnv = tmp : clsEnv e})
  return $ Const i
cls (Unthunk v) = do
  v' <- cls v
  return $ Unthunk v'
cls (Send (S s t) e) = do
  e' <- cls e
  return $ Send (S s t) e'
cls (Recv (S s t) e) = do
  e' <- cls e
  return $ Recv (S s t) e'
cls (Dispatch e1 e2) = do
  e1' <- cls e1
  e2' <- cls e2
  return $ Dispatch e1' e2'
cls (Coleft e) = do
  e' <- cls e
  return $ Coleft e'
cls (Coright e) = do
  e' <- cls e
  return $ Coright e'
cls (Mu (S s t) e) = do
  e' <- cls e
  return $ Mu (S s t) e'
cls (Case e ves) = do
  e' <- cls e
  ves' <-
    forM ves $ \(pat, body) -> do
      pat' <- cls pat
      body' <- cls body
      return (pat', body')
  return $ Case e' ves'
cls (Asc e t) = do
  e' <- cls e
  return $ Asc e' t

freeVar :: Term -> [String]
freeVar (Var s) = [s]
freeVar (Const _) = []
freeVar (Lam (S s t) e) = filter (/= s) (freeVar e)
freeVar (App e v) = freeVar e ++ freeVar v
freeVar (ConsApp v1 v2) = freeVar v1 ++ freeVar v2
freeVar (Ret v) = freeVar v
freeVar (Bind (S s t) e1 e2) = freeVar e1 ++ filter (/= s) (freeVar e2)
freeVar (Thunk e) = freeVar e
freeVar (Unthunk v) = freeVar v
freeVar (Send (S s t) e) = s : freeVar e
freeVar (Recv (S s t) e) = filter (/= s) (freeVar e)
freeVar (Dispatch e1 e2) = freeVar e1 ++ freeVar e2
freeVar (Coleft e) = freeVar e
freeVar (Coright e) = freeVar e
freeVar (Mu (S s t) e) = filter (/= s) (freeVar e)
freeVar (Case e ves) = do
  let efs = freeVar e
  vefss <-
    forM ves $ \(pat, body) -> do
      bound <- freeVar pat
      fs <- freeVar body
      return $ filter (`notElem` bound) fs
  efs ++ vefss
freeVar (Asc e t) = freeVar e
