module Alpha where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Data

alpha :: Expr -> WithEnv Expr
alpha (Var s) = Var <$> alphaString s
alpha (Const (S s t)) = do
  t' <- alphaType t
  return $ Const (S s t')
alpha (Lam (S s t) e) = do
  t' <- alphaType t
  local $ do
    s' <- newNameWith s
    e' <- alpha e
    return $ Lam (S s t') e'
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
    return $ Recv (S s t) e
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
        patEnvOrErr <- liftIO $ runWithEnv (alpha pat) (env {nameEnv = []})
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
alphaType (TConst (S s t)) = do
  t' <- alphaType t
  return $ TConst (S s t')
alphaType (TImp (S s tdom) tcod) = do
  tdom' <- alphaType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- alphaType tcod
    return $ TImp (S s' tdom') tcod'
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

local :: WithEnv a -> WithEnv a
local p = do
  env <- get
  x <- p
  modify (\e -> env {count = count e})
  return x
