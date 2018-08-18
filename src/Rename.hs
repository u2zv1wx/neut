module Rename where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data

renameV :: QuasiValue -> WithEnv QuasiValue
renameV (QuasiValue (i :< ValueVar s)) = do
  t <- ValueVar <$> lookupNameEnv s
  return $ QuasiValue (i :< t)
renameV (QuasiValue (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (renameV . QuasiValue) vs
  let vs'' = map (\(QuasiValue v) -> v) vs'
  return $ QuasiValue (i :< ValueNodeApp s vs'')
renameV (QuasiValue (i :< ValueThunk e)) = do
  e' <- renameC e
  return $ QuasiValue (i :< ValueThunk e')

renameC :: QuasiComp -> WithEnv QuasiComp
renameC (QuasiComp (i :< QuasiCompLam s e)) = do
  local $ do
    s' <- newNameWith s
    QuasiComp e' <- renameC $ QuasiComp e
    return $ QuasiComp (i :< QuasiCompLam s' e')
renameC (QuasiComp (i :< QuasiCompApp e v)) = do
  QuasiComp e' <- renameC $ QuasiComp e
  v' <- renameV v
  return $ QuasiComp (i :< QuasiCompApp e' v')
renameC (QuasiComp (i :< QuasiCompRet v)) = do
  v' <- renameV v
  return $ QuasiComp (i :< QuasiCompRet v')
renameC (QuasiComp (i :< QuasiCompBind s e1 e2)) = do
  QuasiComp e1' <- renameC $ QuasiComp e1
  s' <- newNameWith s
  QuasiComp e2' <- renameC $ QuasiComp e2
  return $ QuasiComp (i :< QuasiCompBind s' e1' e2')
renameC (QuasiComp (i :< QuasiCompUnthunk v)) = do
  v' <- renameV v
  return $ QuasiComp (i :< QuasiCompUnthunk v')
renameC (QuasiComp (i :< QuasiCompMu s e)) = do
  local $ do
    s' <- newNameWith s
    QuasiComp e' <- renameC $ QuasiComp e
    return $ QuasiComp (i :< QuasiCompMu s' e')
renameC (QuasiComp (i :< QuasiCompCase vs ves)) = do
  vs' <- mapM renameV vs
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
            QuasiComp body' <- renameC $ QuasiComp body
            return (pat', body')
  return $ QuasiComp (i :< QuasiCompCase vs' ves')
  -- vs' <- mapM renameV vs
  -- dtree' <- renameDecision dtree
  -- return $ Comp (i :< CompCase vs' dtree')

renameType :: WeakType -> WithEnv WeakType
renameType (WeakTypeVar s) = WeakTypeVar <$> lookupNameEnv s
renameType (WeakTypePosHole i) = return (WeakTypePosHole i)
renameType (WeakTypeNegHole i) = return (WeakTypeNegHole i)
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
renameType (WeakTypeNode s ts) = do
  ts' <- mapM renameType ts
  return $ WeakTypeNode s ts'

renameNodeType ::
     [(Identifier, WeakType)]
  -> WeakType
  -> WithEnv ([(Identifier, WeakType)], WeakType)
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
