module Rename where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data

rename :: WeakTerm -> WithEnv WeakTerm
rename (i :< WeakTermVar s) = do
  t <- WeakTermVar <$> renameString s
  return (i :< t)
rename (i :< WeakTermNodeApp s []) = return (i :< WeakTermNodeApp s [])
rename (i :< WeakTermNodeApp s vs) = do
  vs' <- mapM rename vs
  return (i :< WeakTermNodeApp s vs')
rename (i :< WeakTermLam (s, t) e) = do
  t' <- renameType t
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return (i :< WeakTermLam (s', t') e')
rename (i :< WeakTermApp e v) = do
  e' <- rename e
  v' <- rename v
  return (i :< WeakTermApp e' v')
rename (i :< WeakTermRet v) = do
  v' <- rename v
  return (i :< WeakTermRet v')
rename (i :< WeakTermBind (s, t) e1 e2) = do
  e1' <- rename e1
  s' <- newNameWith s
  t' <- renameType t
  e2' <- rename e2
  return (i :< WeakTermBind (s', t') e1' e2')
rename (i :< WeakTermThunk e) = do
  e' <- rename e
  return (i :< WeakTermThunk e')
rename (i :< WeakTermUnthunk v) = do
  v' <- rename v
  return (i :< WeakTermUnthunk v')
rename (i :< WeakTermMu (s, t) e) = do
  t' <- renameType t
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return (i :< WeakTermMu (s', t') e')
rename (i :< WeakTermCase e ves) = do
  e' <- rename e
  ves' <-
    forM ves $ \(pat, body) ->
      local $ do
        env <- get
        patEnvOrErr <- liftIO $ runWithEnv (renamePat pat) (env {nameEnv = []})
        case patEnvOrErr of
          Left err -> lift $ throwE err
          Right (pat', env') -> do
            put
              (env {nameEnv = nameEnv env' ++ nameEnv env, count = count env'})
            body' <- rename body
            return (pat', body')
  return (i :< WeakTermCase e' ves')
rename (i :< WeakTermAsc e t) = do
  e' <- rename e
  t' <- renameType t
  return (i :< WeakTermAsc e' t')

renameType :: WeakType -> WithEnv WeakType
renameType (WeakTypeVar s) = WeakTypeVar <$> renameString s
renameType (WeakTypeHole i) = return (WeakTypeHole i)
renameType (WeakTypeConst s) = return (WeakTypeConst s)
renameType (WeakTypeUp t) = WeakTypeUp <$> renameType t
renameType (WeakTypeDown t i) = do
  t' <- renameType t
  return $ WeakTypeDown t' i
renameType (WeakTypeUniv level) = return (WeakTypeUniv level)
renameType (WeakTypeForall (Ident s, tdom) tcod) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- renameType tcod
    return (WeakTypeForall (Ident s', tdom') tcod')
renameType (WeakTypeForall (Hole s, tdom) tcod) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- renameType tcod
    return (WeakTypeForall (Hole s', tdom') tcod')
renameType (WeakTypeNode [] tcod) = do
  tcod' <- renameType tcod
  return $ WeakTypeNode [] tcod'
renameType (WeakTypeNode ((x, tdom):xts) tcod) = do
  tdom' <- renameType tdom
  local $ do
    x' <- newNameWith x
    t' <- renameType (WeakTypeNode xts tcod)
    case t' of
      WeakTypeNode yts tcod' -> return $ WeakTypeNode ((x', tdom') : yts) tcod'
      _ -> lift $ throwE $ "malformed type"

renameString :: String -> WithEnv String
renameString s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> lift $ throwE $ "undefined variable: " ++ show s

renamePat :: Pat -> WithEnv Pat
renamePat (i :< PatVar s) = do
  t <- PatVar <$> renamePatString s
  return (i :< t)
renamePat (i :< PatApp s []) = return (i :< PatApp s [])
renamePat (i :< PatApp s vs) = do
  s' <- renamePatString s
  vs' <- mapM renamePat vs
  return (i :< PatApp s' vs')

renamePatString :: String -> WithEnv String
renamePatString s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> newNameWith s
