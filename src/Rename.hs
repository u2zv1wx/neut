module Rename where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data

import qualified Text.Show.Pretty           as Pr

rename :: Term -> WithEnv Term
rename (i :< TermVar s) = do
  t <- TermVar <$> lookupNameEnv s
  return $ i :< t
rename (i :< TermConst s) = return $ i :< TermConst s
rename (i :< TermLam s e) =
  local $ do
    s' <- newNameWith s
    e' <- rename e
    return $ i :< TermLam s' e'
rename (i :< TermApp e v) = do
  e' <- rename e
  v' <- rename v
  return $ i :< TermApp e' v'
rename (i :< TermProduct v1 v2) = do
  v1' <- rename v1
  v2' <- rename v2
  return $ i :< TermProduct v1' v2'
rename (i :< TermInject x v) = do
  v' <- rename v
  return $ i :< TermInject x v'
rename (i :< TermLift v) = do
  v' <- rename v
  return $ i :< TermLift v'
rename (i :< TermBind x e1 e2) = do
  e1' <- rename e1
  local $ do
    x' <- newNameWith x
    e2' <- rename e2
    return $ i :< TermBind x' e1' e2'
rename (i :< TermThunk e) = do
  e' <- rename e
  return $ i :< TermThunk e'
rename (i :< TermUnthunk v) = do
  v' <- rename v
  return $ i :< TermUnthunk v'
rename (i :< TermMu s e) =
  local $ do
    s' <- newNameWith s
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

renameType :: Type -> WithEnv Type
renameType (Fix TypeUnit) = return $ Fix TypeUnit
renameType (Fix (TypeInt i)) = return $ Fix (TypeInt i)
renameType (Fix (TypeVar s)) = do
  t' <- TypeVar <$> lookupNameEnv s
  return $ Fix t'
renameType (Fix (TypeHole i)) = return $ Fix $ TypeHole i
renameType (Fix (TypeUp t)) = do
  t' <- TypeUp <$> renameType t
  return $ Fix t'
renameType (Fix (TypeDown t)) = do
  t' <- renameType t
  return $ Fix $ TypeDown t'
renameType (Fix (TypeUniv level)) = return $ Fix $ TypeUniv level
renameType (Fix (TypeForall (s, tdom) tcod)) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- renameType tcod
    return $ Fix $ TypeForall (s', tdom') tcod'
renameType (Fix (TypeExists (s, tdom) tcod)) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- renameType tcod
    return $ Fix $ TypeExists (s', tdom') tcod'
renameType (Fix (TypeSum labelTypeList)) = do
  let (labelList, typeList) = unzip labelTypeList
  typeList' <- mapM renameType typeList
  return $ Fix $ TypeSum $ zip labelList typeList'
renameType (Fix (TypeNode s ts)) = do
  ts' <- mapM renameType ts
  return $ Fix $ TypeNode s ts'
renameType (Fix (TypeStruct ts)) = do
  ts' <- mapM renameType ts
  return $ Fix $ TypeStruct ts'

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
renamePat (i :< PatConst x) = return $ i :< PatConst x
renamePat (i :< PatVar s) = do
  t <- PatVar <$> lookupNameEnv' s
  return (i :< t)
renamePat (i :< PatProduct v1 v2) = do
  v1' <- renamePat v1
  v2' <- renamePat v2
  return $ i :< PatProduct v1' v2'
renamePat (i :< PatInject x v) = do
  v' <- renamePat v
  return $ i :< PatInject x v'
