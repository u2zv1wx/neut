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
  let unifiedNames = unifyName (nameConstraintEnv env')
  let tenv' =
        map (\(s, t) -> (s, sTypeName unifiedNames $ sType sub t)) $ typeEnv env
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
infer (Lam (S s t) e, Meta {ident = i}) = do
  insTEnv s t
  te <- infer e
  let result = TForall (S s t) te
  insTEnv i result
  return result
infer (App e v, Meta {ident = l}) = do
  te <- infer e
  tv <- infer v
  i <- newName
  insTEnv i (THole i)
  j <- newName
  insTEnv j tv
  insCEnv te (TForall (SHole j tv) (THole i))
  let result = THole i
  insTEnv l result
  return result
infer (ConsApp v1 v2, Meta {ident = l}) = do
  t1 <- infer v1
  t2 <- infer v2
  i <- newName
  insTEnv i (THole i)
  j <- newName
  insTEnv j t2
  insCEnv t1 (TNode (SHole j t2) (THole i))
  let result = THole i
  insTEnv l result
  return result
infer (Ret v, Meta {ident = i}) = do
  tv <- infer v
  let result = TUp tv
  insTEnv i result
  return result
infer (Bind (S s t) e1 e2, Meta {ident = i}) = do
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
infer (Send (S s t) e, Meta {ident = i}) = do
  insTEnv s t
  t <- infer e
  insTEnv i t
  return t
infer (Recv (S s t) e, Meta {ident = i}) = do
  insTEnv s t
  t <- infer e
  insTEnv i t
  return t
infer (Dispatch e1 e2, Meta {ident = i}) = do
  t1 <- infer e1
  t2 <- infer e2
  let result = TCotensor t1 t2
  insTEnv i result
  return result
infer (Coleft e, Meta {ident = i}) = do
  t <- infer e
  t1 <- THole <$> newName
  t2 <- THole <$> newName
  insCEnv t (TCotensor t1 t2)
  insTEnv i t1
  return t1
infer (Coright e, Meta {ident = i}) = do
  t <- infer e
  t1 <- THole <$> newName
  t2 <- THole <$> newName
  insCEnv t (TCotensor t1 t2)
  insTEnv i t2
  return t2
infer (Mu (S s t) e, Meta {ident = i}) = do
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
--  | not (occur s t2)
unify ((t1, THole s):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
--  | not (occur s t1)
unify ((TVar s1, TVar s2):cs)
  | s1 == s2 = unify cs
unify ((TConst s1, TConst s2):cs)
  | s1 == s2 = unify cs
unify ((TNode (S i tdom1) tcod1, TNode (S j tdom2) tcod2):cs)
  | i == j = unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TNode (S i tdom1) tcod1, TNode (SHole j tdom2) tcod2):cs) = do
  insNCEnv (S i tdom1) (SHole j tdom2)
  unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TNode (SHole i tdom1) tcod1, TNode (S j tdom2) tcod2):cs) = do
  insNCEnv (SHole i tdom1) (S j tdom2)
  unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TNode (SHole i tdom1) tcod1, TNode (SHole j tdom2) tcod2):cs) = do
  insNCEnv (SHole i tdom1) (SHole j tdom2)
  unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TForall (S i tdom1) tcod1, TForall (S j tdom2) tcod2):cs)
  | i == j = unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TForall (S i tdom1) tcod1, TForall (SHole j tdom2) tcod2):cs) = do
  insNCEnv (S i tdom1) (SHole j tdom2)
  unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TForall (SHole i tdom1) tcod1, TForall (S j tdom2) tcod2):cs) = do
  insNCEnv (SHole i tdom1) (S j tdom2)
  unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TForall (SHole i tdom1) tcod1, TForall (SHole j tdom2) tcod2):cs) = do
  insNCEnv (SHole i tdom1) (SHole j tdom2)
  unify $ (THole i, THole j) : (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((TCotensor t11 t12, TCotensor t21 t22):cs) =
  unify $ (t11, t21) : (t12, t22) : cs
unify ((TUp t1, TUp t2):cs) = unify $ (t1, t2) : cs
unify ((TDown t1, TDown t2):cs) = unify $ (t1, t2) : cs
unify ((TUniv i, TUniv j):cs) = do
  insLEnv i j
  unify cs
unify ((t1, t2):cs) =
  lift $
  throwE $
  "unification failed for:\n" ++ Pr.ppShow t1 ++ "\nand:\n" ++ Pr.ppShow t2

unifyName :: [(Sym, Sym)] -> [(String, String)]
unifyName [] = []
unifyName ((S i _, S j _):cs)
  | i == j = unifyName cs
unifyName ((SHole i _, S j _):cs) = (i, j) : unifyName cs
unifyName ((S i _, SHole j _):cs) = (j, i) : unifyName cs
unifyName ((SHole i _, SHole j _):cs) = do
  let (xs, ys) = unzip cs
  let replacer target =
        case target of
          S x t ->
            if x == i
              then S j t
              else S x t
          SHole x t ->
            if x == i
              then SHole j t
              else SHole x t
  let xs' = map replacer xs
  let ys' = map replacer ys
  let cs' = zip xs' ys'
  unifyName cs

occur :: String -> Type -> Bool
occur _ (TVar s)                      = False
occur x (THole s)                     = x == s
occur _ (TConst _)                    = False
occur x (TNode (S _ tdom) tcod)       = occur x tdom || occur x tcod
occur x (TNode (SHole _ tdom) tcod)   = occur x tdom || occur x tcod
occur x (TUp t)                       = occur x t
occur x (TDown t)                     = occur x t
occur _ (TUniv i)                     = False
occur x (TForall (S _ tdom) tcod)     = occur x tdom || occur x tcod
occur x (TForall (SHole _ tdom) tcod) = occur x tdom || occur x tcod
occur x (TCotensor t1 t2)             = occur x t1 || occur x t2

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
sType sub (TNode (S s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TNode (S s tdom') tcod'
sType sub (TNode (SHole s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TNode (SHole s tdom') tcod'
sType sub (TUp t) = do
  let t' = sType sub t
  TUp t'
sType sub (TDown t) = do
  let t' = sType sub t
  TDown t'
sType _ (TUniv i) = TUniv i
sType sub (TForall (S s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TForall (S s tdom') tcod'
sType sub (TForall (SHole s tdom) tcod) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  TForall (SHole s tdom') tcod'
sType sub (TCotensor t1 t2) = do
  let t1' = sType sub t1
  let t2' = sType sub t2
  TCotensor t1' t2'

sTypeName :: [(String, String)] -> Type -> Type
sTypeName _ (TVar s) = TVar s
sTypeName _ (THole s) = THole s
sTypeName sub (TConst s) = TConst s
sTypeName sub (TNode (S s tdom) tcod) = do
  let tdom' = sTypeName sub tdom
  let tcod' = sTypeName sub tcod
  TNode (S s tdom') tcod'
sTypeName sub (TNode (SHole s tdom) tcod) = do
  let tdom' = sTypeName sub tdom
  let tcod' = sTypeName sub tcod
  case lookup s sub of
    Just s' -> TNode (S s' tdom') tcod'
    Nothing -> TNode (SHole s tdom') tcod'
sTypeName sub (TUp t) = do
  let t' = sTypeName sub t
  TUp t'
sTypeName sub (TDown t) = do
  let t' = sTypeName sub t
  TDown t'
sTypeName _ (TUniv i) = TUniv i
sTypeName sub (TForall (S s tdom) tcod) = do
  let tdom' = sTypeName sub tdom
  let tcod' = sTypeName sub tcod
  TForall (S s tdom') tcod'
sTypeName sub (TForall (SHole s tdom) tcod) = do
  let tdom' = sTypeName sub tdom
  let tcod' = sTypeName sub tcod
  case lookup s sub of
    Just s' -> TForall (S s' tdom') tcod'
    Nothing -> TForall (SHole s tdom') tcod'
sTypeName sub (TCotensor t1 t2) = do
  let t1' = sTypeName sub t1
  let t2' = sTypeName sub t2
  TCotensor t1' t2'

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (sType s t1, sType s t2))
