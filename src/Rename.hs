module Rename where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data

rename :: Term -> WithEnv Term
rename (i :< TermVar s) = do
  t <- TermVar <$> lookupNameEnv s
  return $ i :< t
rename (i :< TermThunk e) = do
  e' <- rename e
  return $ i :< TermThunk e'
rename (i :< TermLam s e) = do
  local $ do
    s' <- renameArg s
    e' <- rename e
    return $ i :< TermLam s' e'
rename (i :< TermApp e v) = do
  e' <- rename e
  v' <- rename v
  return $ i :< TermApp e' v'
rename (i :< TermLift v) = do
  v' <- rename v
  return $ i :< TermLift v'
rename (i :< TermColift v) = do
  v' <- rename v
  return $ i :< TermColift v'
rename (i :< TermUnthunk v) = do
  v' <- rename v
  return $ i :< TermUnthunk v'
rename (i :< TermMu s e) = do
  local $ do
    s' <- renameArg s
    e' <- rename e
    return $ i :< TermMu s' e'
rename (i :< TermCase vs ves) = do
  vs' <- mapM rename vs
  ves' <-
    forM ves $ \(pat, body) ->
      local $ do
        env <- get
        patEnvOrErr <-
          liftIO $ runWithEnv (mapM renamePat pat) (env {nameEnv = []})
        case patEnvOrErr of
          Left err -> lift $ throwE err
          Right (pat', env') -> do
            put
              (env {nameEnv = nameEnv env' ++ nameEnv env, count = count env'})
            body' <- rename body
            return (pat', body')
  return $ i :< TermCase vs' ves'
rename _ = error "Rename.rename: unreachable"

renameArg :: Arg -> WithEnv Arg
renameArg (ArgIdent s)    = ArgIdent <$> newNameWith s
renameArg (ArgLift arg)   = ArgLift <$> renameArg arg
renameArg (ArgColift arg) = ArgColift <$> renameArg arg

renameType :: Type -> WithEnv Type
renameType (meta :< TypeVar s) = do
  t' <- TypeVar <$> lookupNameEnv s
  return $ meta :< t'
renameType (meta :< TypeHole i) = do
  return $ meta :< TypeHole i
renameType (meta :< TypeUp t) = do
  t' <- TypeUp <$> renameType t
  return $ meta :< t'
renameType (meta :< TypeDown t) = do
  t' <- renameType t
  return $ meta :< TypeDown t'
renameType (meta :< TypeUniv level) = return $ meta :< TypeUniv level
renameType (meta :< TypeForall (s, tdom) tcod) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- renameType tcod
    return $ meta :< TypeForall (s', tdom') tcod'
renameType (meta :< TypeNode s ts) = do
  ts' <- mapM renameType ts
  return $ meta :< TypeNode s ts'

renameNodeType ::
     [(Identifier, Type)] -> Type -> WithEnv ([(Identifier, Type)], Type)
renameNodeType [] t = do
  t' <- renameType t
  return ([], t')
renameNodeType ((i, wt):wts) t = do
  wt' <- renameType wt
  local $ do
    i' <- newNameWith i
    (wts', t') <- renameNodeType wts t
    return ((i', wt') : wts', t')

renamePat :: Pat -> WithEnv Pat
renamePat (i :< PatHole) = return $ i :< PatHole
renamePat (i :< PatVar s) = do
  t <- PatVar <$> lookupNameEnv' s
  return (i :< t)
renamePat (i :< PatApp s []) = return (i :< PatApp s [])
renamePat (i :< PatApp s vs) = do
  vs' <- mapM renamePat vs
  return (i :< PatApp s vs')
