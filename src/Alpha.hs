module Alpha where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data

alpha :: Expr -> WithEnv Expr
alpha (Var s) = Var <$> alphaString s
alpha (Const s) = do
  return $ Const s
alpha (Lam (S s t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alpha e
    return $ Lam (S s' t') e'
alpha (App e v) = do
  e' <- alpha e
  v' <- alpha v
  return $ App e' v'
alpha (VApp v1 v2) = do
  v1' <- alpha v1
  v2' <- alpha v2
  return $ VApp v1' v2'
alpha (Ret v) = do
  v' <- alpha v
  return $ Ret v'
alpha (Bind (S s t) e1 e2) = do
  e1' <- alpha e1
  s' <- newNameWith s
  t' <- alphaType t
  e2' <- alpha e2
  return $ Bind (S s' t') e1' e2'
alpha (Thunk e) = do
  e' <- alpha e
  return $ Thunk e'
alpha (Unthunk v) = do
  v' <- alpha v
  return $ Unthunk v'
alpha (Send (S s t) e) = do
  s' <- alphaString s
  t' <- alphaType t
  e' <- alpha e
  return $ Send (S s' t') e'
alpha (Recv (S s t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alpha e
    return $ Recv (S s' t') e'
alpha (Dispatch e1 e2) = do
  e1' <- alpha e1
  e2' <- alpha e2
  return $ Dispatch e1' e2'
alpha (Coleft e) = do
  e' <- alpha e
  return $ Coleft e'
alpha (Coright e) = do
  e' <- alpha e
  return $ Coright e'
alpha (Mu (S s t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alpha e
    return $ Mu (S s' t') e'
alpha (Case e ves) = do
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
  return $ Case e' ves'
alpha (Asc e t) = do
  e' <- alpha e
  t' <- alphaType t
  return $ Asc e' t'

alphaType :: Type -> WithEnv Type
alphaType (TVar s) = TVar <$> alphaString s
alphaType (THole i) = return $ THole i
alphaType (TConst s) = do
  return $ TConst s
alphaType (TNode (S s tdom) tcod) = do
  tdom' <- alphaType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- alphaType tcod
    return $ TNode (S s' tdom') tcod'
alphaType (TUp t) = TUp <$> alphaType t
alphaType (TDown t) = TDown <$> alphaType t
alphaType (TUniv level) = return $ TUniv level
alphaType (TForall (S s tdom) tcod) = do
  tdom' <- alphaType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- alphaType tcod
    return $ TForall (S s' tdom') tcod'
alphaType (TCotensor t1 t2) = do
  t1' <- alphaType t1
  t2' <- alphaType t2
  return $ TCotensor t1' t2'

alphaString :: String -> WithEnv String
alphaString s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> lift $ throwE $ "undefined variable: " ++ show s

alphaPat :: Expr -> WithEnv Expr
alphaPat (Var s) = Var <$> alphaPatString s
alphaPat (Const s) = return $ Const s
alphaPat (Lam (S s t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alphaPat e
    return $ Lam (S s' t') e'
alphaPat (App e v) = do
  e' <- alphaPat e
  v' <- alphaPat v
  return $ App e' v'
alphaPat (VApp v1 v2) = do
  v1' <- alphaPat v1
  v2' <- alphaPat v2
  return $ VApp v1' v2'
alphaPat (Ret v) = do
  v' <- alphaPat v
  return $ Ret v'
alphaPat (Bind (S s t) e1 e2) = do
  e1' <- alphaPat e1
  s' <- newNameWith s
  t' <- alphaType t
  e2' <- alphaPat e2
  return $ Bind (S s' t') e1' e2'
alphaPat (Thunk e) = do
  e' <- alphaPat e
  return $ Thunk e'
alphaPat (Unthunk v) = do
  v' <- alphaPat v
  return $ Unthunk v'
alphaPat (Send (S s t) e) = do
  s' <- alphaPatString s
  t' <- alphaType t
  e' <- alphaPat e
  return $ Send (S s' t') e'
alphaPat (Recv (S s t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alphaPat e
    return $ Recv (S s t) e
alphaPat (Dispatch e1 e2) = do
  e1' <- alphaPat e1
  e2' <- alphaPat e2
  return $ Dispatch e1' e2'
alphaPat (Coleft e) = do
  e' <- alphaPat e
  return $ Coleft e'
alphaPat (Coright e) = do
  e' <- alphaPat e
  return $ Coright e'
alphaPat (Mu (S s t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alphaPat e
    return $ Mu (S s' t') e'
alphaPat (Case e ves) = do
  e' <- alphaPat e
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
            body' <- alphaPat body
            return (pat', body')
  return $ Case e' ves'
alphaPat (Asc e t) = do
  e' <- alphaPat e
  t' <- alphaType t
  return $ Asc e' t'

alphaPatString :: String -> WithEnv String
alphaPatString s = do
  env <- get
  case lookup s (nameEnv env) of
    Just s' -> return s'
    Nothing -> newNameWith s

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x
