module Typing
  ( check
  , unify
  ) where

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data

check :: MTerm -> WithEnv ()
check e = do
  _ <- infer e
  env <- get
  sub <- unify $ constraintEnv env
  liftIO $ putStrLn $ Pr.ppShow sub
  env' <- get
  let tenv' = map (\(s, t) -> (s, sType sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: MTerm -> WithEnv Type
infer (Var s, Meta {ident = i}) = do
  mt <- lookupTEnv s
  case mt of
    Just t -> do
      insTEnv i t
      return t
    Nothing -> do
      new <- THole <$> newName
      insTEnv s new
      insTEnv i new
      return new
infer (Const s, Meta {ident = i}) = do
  mt <- lookupVEnv s
  case mt of
    Just t -> do
      insTEnv i t
      return t
    Nothing -> lift $ throwE $ "const " ++ s ++ " is not defined"
infer (Lam (s, t) e, Meta {ident = i}) = do
  insTEnv s t
  te <- infer e
  let result = TForall (s, t) te
  insTEnv i result
  return result
infer (App e v, Meta {ident = l}) = do
  te <- infer e
  tv <- infer v
  i <- newName
  insTEnv i (THole i)
  j <- newName
  insTEnv j tv
  insCEnv te (TForall (j, tv) (THole i))
  let result = THole i
  insTEnv l result
  return result
infer (Ret v, Meta {ident = i}) = do
  tv <- infer v
  let result = TUp tv
  insTEnv i result
  return result
infer (Bind (s, t) e1 e2, Meta {ident = i}) = do
  insTEnv s t
  t1 <- infer e1
  t2 <- infer e2
  insCEnv (TUp t) t1
  insTEnv i t2
  return t2
infer (Thunk e, Meta {ident = i}) = do
  t <- infer e
  let result = TDown t
  insTEnv i result
  return result
infer (Unthunk v, Meta {ident = l}) = do
  t <- infer v
  i <- newName
  insCEnv t (TDown (THole i))
  let result = THole i
  insTEnv l result
  return result
infer (Mu (s, t) e, Meta {ident = i}) = do
  insTEnv s t
  te <- infer e
  insCEnv (TDown te) t
  insTEnv i te
  return te
infer (Case e ves, Meta {ident = i}) = do
  t <- infer e
  let (vs, es) = unzip ves
  tvs <- mapM infer vs
  forM_ tvs $ \tv -> insCEnv t tv
  ans <- THole <$> newName
  tes <- mapM infer es
  forM_ tes $ \te -> insCEnv ans te
  insTEnv i ans
  return ans
infer (Asc e t, Meta {ident = i}) = do
  te <- infer e
  insCEnv t te
  insTEnv i te
  return te

type Subst = [(String, Type)]

type Constraint = [(Type, Type)]

unify :: Constraint -> WithEnv Subst
unify [] = return []
unify ((THole s, t2):cs) = do
  sub <- unify (sConstraint [(s, t2)] cs)
  return $ compose sub [(s, t2)]
unify ((t1, THole s):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
unify ((TVar s1, TVar s2):cs)
  | s1 == s2 = unify cs
unify ((TConst s1, TConst s2):cs)
  | s1 == s2 = unify cs
unify ((TForall (i, tdom1) tcod1, TForall (j, tdom2) tcod2):cs)
  | i == j = unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TUp t1, TUp t2):cs) = unify $ (t1, t2) : cs
unify ((TDown t1, TDown t2):cs) = unify $ (t1, t2) : cs
unify ((TUniv i, TUniv j):cs) = do
  insLEnv i j
  unify cs
unify ((t1, t2):cs) =
  lift $
  throwE $
  "unification failed for:\n" ++ Pr.ppShow t1 ++ "\nand:\n" ++ Pr.ppShow t2

compose :: Subst -> Subst -> Subst
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (sType s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'

sType :: Subst -> Type -> Type
sType _ (TVar s) = TVar s
sType sub (THole s) =
  case lookup s sub of
    Nothing -> THole s
    Just t  -> t
sType sub (TConst s) = TConst s
sType sub (TUp t) = do
  let t' = sType sub t
  TUp t'
sType sub (TDown t) = do
  let t' = sType sub t
  TDown t'
sType _ (TUniv i) = TUniv i
sType sub (TForall (s, tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TForall (s, tdom') tcod'

sTypeName :: [(String, String)] -> Type -> Type
sTypeName _ (TVar s) = TVar s
sTypeName _ (THole s) = THole s
sTypeName sub (TConst s) = TConst s
sTypeName sub (TUp t) = do
  let t' = sTypeName sub t
  TUp t'
sTypeName sub (TDown t) = do
  let t' = sTypeName sub t
  TDown t'
sTypeName _ (TUniv i) = TUniv i
sTypeName sub (TForall (s, tdom) tcod) = do
  let tdom' = sTypeName sub tdom
  let tcod' = sTypeName sub tcod
  TForall (s, tdom') tcod'

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (sType s t1, sType s t2))
