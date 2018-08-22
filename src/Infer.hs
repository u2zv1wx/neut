module Infer
  ( check
  , unify
  ) where

import           Control.Monad
import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import qualified Text.Show.Pretty           as Pr

import           Data

check :: Identifier -> Term -> WithEnv ()
check main e = do
  (t, pol) <- infer e
  insTypeEnv main t -- insert the type of main function
  insPolEnv main pol
  env <- get
  sub <- unify $ constraintEnv env
  polSub <- unifyPol $ polConstraintEnv env
  aenv <- gets argConstraintEnv
  argSub <- unifyArg aenv
  let tenv' = map (\(s, t) -> (s, sArgType argSub $ sType sub t)) $ typeEnv env
  let polEnv' = map (\(s, t) -> (s, sPol polSub t)) $ polEnv env
  modify (\e -> e {typeEnv = tenv', polEnv = polEnv', constraintEnv = []})

infer :: Term -> WithEnv (Type, Polarity)
infer (meta :< TermVar s) = do
  mt <- lookupTypeEnv s
  mpol <- lookupPolEnv s
  case (mt, mpol) of
    (Just t, Just pol) -> do
      insTypeEnv meta t
      insPolEnv meta pol
      return (t, pol)
    _ -> lift $ throwE $ "undefined variable: " ++ s
infer (meta :< TermThunk e) = do
  (t, pol) <- infer e
  let result = Fix $ TypeDown t
  insPolConstraintEnv pol PolarityNegative
  insTypeEnv meta result
  insPolEnv meta PolarityPositive
  return (result, PolarityPositive)
infer (meta :< TermLam s e) = do
  (tdom, polDom) <- inferArg s
  (te, polCod) <- infer e
  let result = Fix $ TypeForall (s, tdom) te
  insPolConstraintEnv polDom polCod
  insTypeEnv meta result
  insPolEnv meta polCod
  return (result, polCod)
infer (meta :< TermApp e v) = do
  (te, polFun) <- infer e
  (tv, polArg) <- infer v
  i <- newName
  let result = Fix $ TypeHole i
  j <- newName
  argMeta <- newNameWith "meta"
  insTypeEnv argMeta tv
  insPolEnv argMeta polArg
  insConstraintEnv te (Fix $ TypeForall (argMeta :< ArgHole j, tv) result)
  insPolConstraintEnv polFun polArg
  insTypeEnv meta result
  insPolEnv meta polArg
  return (result, polArg)
infer (meta :< TermLift v) = do
  (tv, pol) <- infer v
  insPolConstraintEnv pol PolarityPositive
  insTypeEnv meta $ Fix $ TypeUp tv
  insPolEnv meta PolarityNegative
  return (Fix $ TypeUp tv, PolarityNegative)
infer (meta :< TermColift v) = do
  (tv, pol) <- infer v
  insPolConstraintEnv pol PolarityNegative
  insTypeEnv meta $ Fix $ TypeDown tv
  insPolEnv meta PolarityPositive
  return (Fix $ TypeDown tv, PolarityPositive)
infer (meta :< TermUnthunk v) = do
  (t, pol) <- infer v
  i <- newName
  let result = Fix $ TypeHole i
  insConstraintEnv t (Fix $ TypeDown result)
  insPolConstraintEnv pol PolarityPositive
  insTypeEnv meta result
  insPolEnv meta PolarityNegative
  return (result, PolarityNegative)
infer (meta :< TermMu s e) = do
  (trec, polArg) <- inferArg s
  -- insTypeEnv ident trec
  (te, polBody) <- infer e
  insConstraintEnv (Fix $ TypeDown te) trec
  insPolConstraintEnv polArg PolarityPositive
  insPolConstraintEnv polBody PolarityNegative
  insTypeEnv meta te
  insPolEnv meta PolarityNegative
  return (te, PolarityNegative)
infer (meta :< TermCase vs vses) = do
  tps <- mapM infer vs -- type-polarity-list
  let (vss, es) = unzip vses
  tvss <- mapM (mapM inferPat) vss
  forM_ tvss $ \tvs -> do
    forM_ (zip tps tvs) $ \((t1, pol1), (t2, pol2)) -> do
      insConstraintEnv t1 t2
      insPolConstraintEnv pol1 pol2
  ans <- TypeHole <$> newName
  tes <- mapM (infer) es
  forM_ tes $ \(te, pol) -> do
    insConstraintEnv (Fix $ ans) te
    insPolConstraintEnv pol PolarityNegative
  insTypeEnv meta (Fix ans)
  insPolEnv meta PolarityNegative
  return (Fix $ ans, PolarityNegative)
infer t = error $ "Infer.infer: illegal argument: " ++ Pr.ppShow t

inferPat :: Pat -> WithEnv (Type, Polarity)
inferPat (meta :< PatHole) = do
  t <- TypeHole <$> newName
  insTypeEnv meta $ Fix t
  j <- newName
  insPolEnv meta (PolarityHole j)
  return (Fix t, PolarityHole j)
inferPat (meta :< PatVar s) = do
  mt <- lookupTypeEnv s
  mpol <- lookupPolEnv s
  case (mt, mpol) of
    (Just t, Just pol) -> do
      insTypeEnv meta t
      insPolEnv meta pol
      return (t, pol)
    _ -> do
      i <- newName
      j <- newName
      insTypeEnv s $ Fix $ TypeHole i
      insPolEnv s (PolarityHole j)
      insTypeEnv meta (Fix (TypeHole i))
      insPolEnv meta (PolarityHole j)
      return (Fix (TypeHole i), PolarityHole j)
inferPat (meta :< PatApp s vs) = do
  mt <- lookupVEnv s
  case mt of
    Nothing -> lift $ throwE $ "const " ++ s ++ " is not defined"
    Just (_, xts, t) -> do
      tvs <- mapM inferPat vs
      -- need to add explicit parametrization
      forM_ (zip xts tvs) $ \(xt, (t2, pol)) -> do
        insConstraintEnv (snd xt) t2
        insPolConstraintEnv pol PolarityPositive
      insTypeEnv meta t
      return (t, PolarityPositive)

inferArg :: Arg -> WithEnv (Type, Polarity)
inferArg (meta :< ArgIdent x) = do
  t <- newName
  j <- newName
  insPolEnv x (PolarityHole j)
  insTypeEnv meta (Fix (TypeHole t))
  insPolEnv meta (PolarityHole j)
  return (Fix $ TypeHole t, PolarityHole j)
inferArg (meta :< ArgLift arg) = do
  (t, pol) <- inferArg arg
  insPolConstraintEnv pol PolarityPositive
  insTypeEnv meta (Fix (TypeUp t))
  insPolEnv meta pol
  return (Fix $ TypeUp t, PolarityNegative)
inferArg (meta :< ArgColift arg) = do
  (t, pol) <- inferArg arg
  insPolConstraintEnv pol PolarityNegative
  insPolEnv meta pol
  insTypeEnv meta (Fix (TypeDown t))
  return (Fix $ TypeDown t, PolarityPositive)
inferArg _ = error "Infer.inferArg: illegal argument"

type Subst = [(String, Type)]

type Constraint = [(Type, Type)]

unify :: Constraint -> WithEnv Subst
unify [] = return []
unify ((Fix (TypeHole s), t2):cs) = do
  sub <- unify (sConstraint [(s, t2)] cs)
  return $ compose sub [(s, t2)]
unify ((t1, Fix (TypeHole s)):cs) = do
  sub <- unify (sConstraint [(s, t1)] cs)
  return $ compose sub [(s, t1)]
unify ((Fix (TypeVar s1), Fix (TypeVar s2)):cs)
  | s1 == s2 = unify cs
unify (((Fix (TypeForall (arg1, tdom1) tcod1)), Fix (TypeForall (arg2, tdom2) tcod2)):cs) = do
  insArgConstraintEnv arg1 arg2
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((Fix (TypeNode x ts1), Fix (TypeNode y ts2)):cs)
  | x == y = unify $ (zip ts1 ts2) ++ cs
unify ((Fix (TypeUp t1), Fix (TypeUp t2)):cs) = do
  unify $ (t1, t2) : cs
unify ((Fix (TypeDown t1), Fix (TypeDown t2)):cs) = do
  unify $ (t1, t2) : cs
unify ((Fix (TypeUniv i), Fix (TypeUniv j)):cs) = do
  insLEnv i j
  unify cs
unify ((t1, t2):_) =
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
sType _ (Fix (TypeVar s)) = Fix $ TypeVar s
sType sub (Fix (TypeHole s)) =
  case lookup s sub of
    Nothing -> Fix $ TypeHole s
    Just t  -> t
sType sub (Fix (TypeUp t)) = do
  let t' = sType sub t
  Fix $ TypeUp t'
sType sub (Fix (TypeDown t)) = do
  let t' = sType sub t
  Fix $ TypeDown t'
sType _ (Fix (TypeUniv i)) = Fix $ TypeUniv i
sType sub (Fix (TypeForall (s, tdom) tcod)) = do
  let tdom' = sType sub tdom
  let tcod' = sType sub tcod
  Fix $ TypeForall (s, tdom') tcod'
sType sub (Fix (TypeNode s ts)) = do
  let ts' = map (sType sub) ts
  Fix $ TypeNode s ts'

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (sType s t1, sType s t2))

type PolSubst = [(String, Polarity)]

type PolConstraint = [(Polarity, Polarity)]

unifyPol :: PolConstraint -> WithEnv PolSubst
unifyPol [] = return []
unifyPol ((PolarityHole x, pol2):cs) = do
  sub <- unifyPol (sPolConstraint [(x, pol2)] cs)
  return $ composePol sub [(x, pol2)]
unifyPol ((pol1, PolarityHole y):cs) = do
  sub <- unifyPol (sPolConstraint [(y, pol1)] cs)
  return $ composePol sub [(y, pol1)]
unifyPol ((PolarityPositive, PolarityPositive):cs) = unifyPol cs
unifyPol ((PolarityNegative, PolarityNegative):cs) = unifyPol cs
unifyPol ((pol1, pol2):_) =
  lift $
  throwE $
  "unification failed for:\n" ++ Pr.ppShow pol1 ++ "\nand:\n" ++ Pr.ppShow pol2

composePol :: PolSubst -> PolSubst -> PolSubst
composePol s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (sPol s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'

sPol :: PolSubst -> Polarity -> Polarity
sPol sub (PolarityHole x) = do
  case lookup x sub of
    Nothing  -> PolarityHole x
    Just pol -> pol
sPol _ PolarityPositive = PolarityPositive
sPol _ PolarityNegative = PolarityNegative

sPolConstraint :: PolSubst -> PolConstraint -> PolConstraint
sPolConstraint s = map (\(t1, t2) -> (sPol s t1, sPol s t2))

type ArgSubst = [(String, Arg)]

type ArgConstraint = [(Arg, Arg)]

unifyArg :: ArgConstraint -> WithEnv ArgSubst
unifyArg [] = return []
unifyArg ((_ :< ArgHole x, pol2):cs) = do
  sub <- unifyArg (sArgConstraint [(x, pol2)] cs)
  return $ composeArg sub [(x, pol2)]
unifyArg ((pol1, _ :< ArgHole y):cs) = do
  sub <- unifyArg (sArgConstraint [(y, pol1)] cs)
  return $ composeArg sub [(y, pol1)]
unifyArg ((_ :< ArgIdent _, _ :< ArgIdent _):cs) = unifyArg cs
unifyArg ((_ :< ArgLift arg1, _ :< ArgLift arg2):cs) =
  unifyArg $ (arg1, arg2) : cs
unifyArg ((_ :< ArgColift arg1, _ :< ArgColift arg2):cs) =
  unifyArg $ (arg1, arg2) : cs
unifyArg ((pol1, pol2):_) =
  lift $
  throwE $
  "unification failed for:\n" ++ Pr.ppShow pol1 ++ "\nand:\n" ++ Pr.ppShow pol2

composeArg :: ArgSubst -> ArgSubst -> ArgSubst
composeArg s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (sArg s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'

sArg :: ArgSubst -> Arg -> Arg
sArg sub (i :< ArgHole x) = do
  case lookup x sub of
    Nothing  -> i :< ArgHole x
    Just pol -> pol
sArg _ (i :< ArgIdent x) = i :< ArgIdent x
sArg sub (i :< ArgLift arg) = i :< ArgLift (sArg sub arg)
sArg sub (i :< ArgColift arg) = i :< ArgColift (sArg sub arg)

sArgConstraint :: ArgSubst -> ArgConstraint -> ArgConstraint
sArgConstraint s = map (\(t1, t2) -> (sArg s t1, sArg s t2))

sArgType :: ArgSubst -> Type -> Type
sArgType _ (Fix (TypeVar s)) = Fix $ TypeVar s
sArgType _ (Fix (TypeHole s)) = Fix $ TypeHole s
sArgType sub (Fix (TypeUp t)) = do
  let t' = sArgType sub t
  Fix $ TypeUp t'
sArgType sub (Fix (TypeDown t)) = do
  let t' = sArgType sub t
  Fix $ TypeDown t'
sArgType _ (Fix (TypeUniv i)) = Fix $ TypeUniv i
sArgType sub (Fix (TypeForall (s, tdom) tcod)) = do
  let tdom' = sArgType sub tdom
  let tcod' = sArgType sub tcod
  Fix $ TypeForall (sArg sub s, tdom') tcod'
sArgType sub (Fix (TypeNode s ts)) = do
  let ts' = map (sArgType sub) ts
  Fix $ TypeNode s ts'
