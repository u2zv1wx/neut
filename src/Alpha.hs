module Alpha where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data

alpha :: WeakTerm -> WithEnv WeakTerm
alpha (i :< WeakTermVar s) = do
  t <- WeakTermVar <$> alphaString s
  return (i :< t)
alpha (i :< WeakTermConst s) = return (i :< WeakTermConst s)
alpha (i :< WeakTermNodeApp v1 v2) = do
  v1' <- alpha v1
  v2' <- alpha v2
  return (i :< WeakTermNodeApp v1' v2')
alpha (i :< WeakTermLam (s, t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alpha e
    return (i :< WeakTermLam (s', t') e')
alpha (i :< WeakTermApp e v) = do
  e' <- alpha e
  v' <- alpha v
  return (i :< WeakTermApp e' v')
alpha (i :< WeakTermRet v) = do
  v' <- alpha v
  return (i :< WeakTermRet v')
alpha (i :< WeakTermBind (s, t) e1 e2) = do
  e1' <- alpha e1
  s' <- newNameWith s
  t' <- alphaType t
  e2' <- alpha e2
  return (i :< WeakTermBind (s', t') e1' e2')
alpha (i :< WeakTermThunk e) = do
  e' <- alpha e
  return (i :< WeakTermThunk e')
alpha (i :< WeakTermUnthunk v) = do
  v' <- alpha v
  return (i :< WeakTermUnthunk v')
alpha (i :< WeakTermMu (s, t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alpha e
    return (i :< WeakTermMu (s', t') e')
alpha (i :< WeakTermCase e ves) = do
  e' <- alpha e
  ves' <-
    forM ves $ \(pat, body) ->
      local $ do
        env <- get
        patEnvOrErr <- liftIO $ runWithEnv (alphaPat pat) (env {nameEnv = []})
        case patEnvOrErr of
          Left err -> lift $ throwE err
          Right (pat', env') -> do
            put
              (env {nameEnv = nameEnv env' ++ nameEnv env, count = count env'})
            body' <- alpha body
            return (pat', body')
  return (i :< WeakTermCase e' ves')
alpha (i :< WeakTermAsc e t) = do
  e' <- alpha e
  t' <- alphaType t
  return (i :< WeakTermAsc e' t')

alphaType :: WeakType -> WithEnv WeakType
alphaType (WeakTypeVar s) = WeakTypeVar <$> alphaString s
alphaType (WeakTypeHole i) = return (WeakTypeHole i)
alphaType (WeakTypeConst s) = return (WeakTypeConst s)
alphaType (WeakTypeUp t) = WeakTypeUp <$> alphaType t
alphaType (WeakTypeDown t) = WeakTypeDown <$> alphaType t
alphaType (WeakTypeUniv level) = return (WeakTypeUniv level)
alphaType (WeakTypeForall (s, tdom) tcod) = do
  tdom' <- alphaType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- alphaType tcod
    return (WeakTypeForall (s', tdom') tcod')
alphaType (WeakTypeNode (s, tdom) tcod) = do
  tdom' <- alphaType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- alphaType tcod
    return (WeakTypeNode (s', tdom') tcod')

alphaString :: String -> WithEnv String
alphaString s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> lift $ throwE $ "undefined variable: " ++ show s

alphaPat :: Pat -> WithEnv Pat
alphaPat (i :< PatVar s) = do
  t <- PatVar <$> alphaPatString s
  return (i :< t)
alphaPat (i :< PatConst s) = return (i :< PatConst s)
alphaPat (i :< PatApp e v) = do
  e' <- alphaPat e
  v' <- alphaPat v
  return (i :< PatApp e' v')

alphaPatString :: String -> WithEnv String
alphaPatString s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> newNameWith s
