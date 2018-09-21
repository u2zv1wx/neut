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
import           Data.List                  (nub)
import           Data.Maybe

check :: Identifier -> Neut -> WithEnv ()
check main e = do
  t <- infer e
  insTypeEnv main t -- insert the type of main function
  env <- get
  sub <- unifyLoop (constraintEnv env) 0
  let tenv' = map (\(s, t) -> (s, subst sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})

infer :: Neut -> WithEnv Neut
infer (meta :< NeutVar s) = do
  t <- lookupTypeEnv' s
  returnMeta meta t
infer (meta :< NeutPi (s, tdom) tcod) = inferBinder meta s tdom tcod
infer (meta :< NeutPiIntro (s, tdom) e) = do
  insTypeEnv s tdom
  udom <- infer tdom
  tcod <- infer e
  ucod <- infer tcod
  insConstraintEnv udom ucod
  wrapTypeWithUniv udom (NeutPi (s, tdom) tcod) >>= returnMeta meta
infer (meta :< NeutPiElim e1 e2) = do
  tPi <- infer e1 -- forall (x : tdom). tcod
  tdom <- infer e2
  udom <- infer tdom
  codName <- newName
  tcod <- wrapType $ NeutHole codName
  ucod <- infer tcod
  insConstraintEnv udom ucod
  x <- newNameOfType tdom
  typeMeta2 <- newNameWith "meta"
  insTypeEnv typeMeta2 udom
  insConstraintEnv tPi (typeMeta2 :< NeutPi (x, tdom) tcod) -- t1 == forall (x : tdom). tcod
  insEqEnv $ EquationPiElim tPi e2 codName
  returnMeta meta $ explicitSubst tcod [(x, e2)]
infer (meta :< NeutSigma (s, tdom) tcod) = inferBinder meta s tdom tcod
infer (meta :< NeutSigmaIntro e1 e2) = do
  t1 <- infer e1 -- A
  t2 <- infer e2 -- B {x := e1}
  u1 <- infer t1
  u2 <- infer t2
  insConstraintEnv u1 u2
  t2nosub <- newHole -- B
  x <- newNameOfType t1
  let t2sub = explicitSubst t2nosub [(x, e1)]
  insConstraintEnv t2 t2sub
  wrapTypeWithUniv u1 (NeutSigma (x, t1) t2nosub) >>= returnMeta meta -- Sigma (x : A). B
infer (meta :< NeutSigmaElim e1 (x, y) e2) = do
  t1 <- infer e1
  u1 <- infer t1
  tx <- newHole
  ux <- infer tx
  ty <- newHole
  uy <- infer ty
  t2 <- infer e2
  u2 <- infer t2
  insTypeEnv x tx
  insTypeEnv y ty
  insConstraintEnv u1 u2
  insConstraintEnv u1 ux
  insConstraintEnv ux uy
  sigmaType <- wrapType $ NeutSigma (x, tx) ty
  insConstraintEnv t1 sigmaType
  z <- newNameOfType t1
  pair <- constructPair x y
  holeName <- newName
  resultHole <- wrapType $ NeutHole holeName
  insConstraintEnv t2 $ explicitSubst resultHole [(z, pair)]
  insEqEnv $ EquationSigmaElim e1 (t2, (x, y)) holeName
  returnMeta meta $ explicitSubst resultHole [(z, e1)]
infer (meta :< NeutMu s e) = do
  trec <- newHole
  insTypeEnv s trec
  te <- infer e
  insConstraintEnv te trec
  returnMeta meta te
infer (meta :< NeutTop) = do
  hole <- newName
  wrap (NeutUniv (UnivLevelHole hole)) >>= returnMeta meta
infer (meta :< NeutTopIntro) = wrapType NeutTop >>= returnMeta meta
infer (meta :< NeutIndex _) = do
  hole <- newName
  wrap (NeutUniv (UnivLevelHole hole)) >>= returnMeta meta
infer (meta :< NeutIndexIntro l) = do
  k <- lookupKind l
  t <- wrapType $ NeutIndex k
  returnMeta meta t
infer (_ :< NeutIndexElim _ []) = lift $ throwE "empty branch"
infer (meta :< NeutIndexElim e branchList) = do
  t <- infer e
  let (labelList, es) = unzip branchList
  tls <- mapM inferLabel labelList
  constrainList tls
  insConstraintEnv t $ head tls
  tes <- mapM infer es
  constrainList tes
  kindSet <- lookupIndexSet $ head labelList
  if length kindSet <= length (nub labelList)
    then returnMeta meta $ head tes
    else lift $ throwE "incomplete pattern"
infer (meta :< NeutUniv l) =
  wrap (NeutUniv (UnivLevelNext l)) >>= returnMeta meta
infer (meta :< NeutHole _) = do
  hole <- newName
  wrap (NeutUniv (UnivLevelHole hole)) >>= returnMeta meta
infer (_ :< NeutSubst e _) = infer e

inferLabel :: Identifier -> WithEnv Neut
inferLabel name = do
  k <- lookupKind name
  wrapType $ NeutIndex k

constrainList :: [Neut] -> WithEnv ()
constrainList [] = return ()
constrainList [_] = return ()
constrainList (t1:t2:ts) = do
  insConstraintEnv t1 t2
  constrainList $ t2 : ts

inferBinder :: Identifier -> Identifier -> Neut -> Neut -> WithEnv Neut
inferBinder meta s tdom tcod = do
  udom <- infer tdom
  insTypeEnv s tdom
  ucod <- infer tcod
  insConstraintEnv udom ucod
  returnMeta meta udom

constructPair :: Identifier -> Identifier -> WithEnv Neut
constructPair x y = do
  eMeta <- newName
  xMeta <- newName
  yMeta <- newName
  let pair = eMeta :< NeutSigmaIntro (xMeta :< NeutVar x) (yMeta :< NeutVar y)
  _ <- infer pair
  return pair

newNameOfType :: Neut -> WithEnv Identifier
newNameOfType t = do
  i <- newName
  insTypeEnv i t
  return i

explicitSubst :: Neut -> [(Identifier, Neut)] -> Neut
explicitSubst e1 sub = "" :< NeutSubst e1 sub

newHole :: WithEnv Neut
newHole = do
  i <- newName
  wrapType $ NeutHole i

returnMeta :: Identifier -> Neut -> WithEnv Neut
returnMeta meta t = do
  insTypeEnv meta t
  return t

type Constraint = [(Neut, Neut)]

unifyLoop :: Constraint -> Int -> WithEnv Subst
unifyLoop [] _ = return []
unifyLoop ((e1, e2):cs) loopCount = do
  (tmpSubst, tmpConstraint) <- unify ((reduce e1, reduce e2) : cs)
  case (tmpSubst, tmpConstraint) of
    (s, []) -> return s
    (s, (e1', e2'):cs') -> do
      let loopCount' = nextLoopCount (length cs) (length cs') loopCount
      if didFinishLoop (length cs') loopCount'
        then do
          liftIO $ putStrLn $ "failing unification. subst:\n" ++ Pr.ppShow s
          unificationFailed (reduce e1) (reduce e2) cs'
        else do
          env <- get
          let eqEnv' = map (substEq s) $ eqEnv env
          (eqEnv'', additionalSubst) <- unifyEq eqEnv'
          modify (\e -> e {eqEnv = eqEnv''})
          let newConstraints = sConstraint additionalSubst (cs' ++ [(e1', e2')])
          s' <- unifyLoop newConstraints loopCount'
          return (s ++ s')

unificationFailed :: Neut -> Neut -> Constraint -> WithEnv Subst
unificationFailed e1 e2 cs = do
  env <- get
  lift $
    throwE $
    "unification failed for\n" ++
    Pr.ppShow e1 ++
    "\nand\n" ++
    Pr.ppShow e2 ++
    "\nwith constraints:\n" ++
    Pr.ppShow cs ++ "\ntypeEnv:\n" ++ Pr.ppShow (typeEnv env)

nextLoopCount :: Int -> Int -> Int -> Int
nextLoopCount i j loopCount = do
  let lenOld = i + 1
  let lenNew = j + 1
  if lenOld <= lenNew
    then loopCount + 1
    else 0

didFinishLoop :: Int -> Int -> Bool
didFinishLoop j loopCount' = loopCount' >= j + 2

unify :: Constraint -> WithEnv (Subst, Constraint)
unify [] = return ([], [])
unify ((_ :< NeutHole s, t2):cs) = do
  (sub, cs') <- unify (sConstraint [(s, t2)] cs)
  return (compose sub [(s, t2)], cs')
unify ((t1, _ :< NeutHole s):cs) = do
  (sub, cs') <- unify (sConstraint [(s, t1)] cs)
  return (compose sub [(s, t1)], cs')
unify ((_ :< NeutVar s1, _ :< NeutVar s2):cs)
  | s1 == s2 = unify cs
unify ((_ :< NeutPi (_, tdom1) tcod1, _ :< NeutPi (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutSigma (_, tdom1) tcod1, _ :< NeutSigma (_, tdom2) tcod2):cs) =
  unify $ (tdom1, tdom2) : (tcod1, tcod2) : cs
unify ((_ :< NeutTop, _ :< NeutTop):cs) = unify cs
unify ((_ :< NeutIndex l1, _ :< NeutIndex l2):cs)
  | l1 == l2 = unify cs
unify ((_ :< NeutUniv i, _ :< NeutUniv j):cs) = do
  insUnivConstraintEnv i j
  unify cs
unify cs = return ([], cs)

sConstraint :: Subst -> Constraint -> Constraint
sConstraint s = map (\(t1, t2) -> (subst s t1, subst s t2))

-- e is strong <=> e does not contain any holes
isStrong :: Neut -> Bool
isStrong (_ :< NeutVar _) = True
isStrong (_ :< NeutPi (_, tdom) tcod) = isStrong tdom && isStrong tcod
isStrong (_ :< NeutPiIntro (_, tdom) e) = isStrong tdom && isStrong e
isStrong (_ :< NeutPiElim e1 e2) = isStrong e1 && isStrong e2
isStrong (_ :< NeutSigma (_, tdom) tcod) = isStrong tdom && isStrong tcod
isStrong (_ :< NeutSigmaIntro e1 e2) = isStrong e1 && isStrong e2
isStrong (_ :< NeutSigmaElim e1 (_, _) e2) = isStrong e1 && isStrong e2
isStrong (_ :< NeutMu _ e) = isStrong e
isStrong (_ :< NeutTop) = True
isStrong (_ :< NeutTopIntro) = True
isStrong (_ :< NeutIndex _) = True
isStrong (_ :< NeutIndexIntro _) = True
isStrong (_ :< NeutIndexElim e1 branchList) = do
  let (_, es) = unzip branchList
  isStrong e1 && all isStrong es
isStrong (_ :< NeutUniv _) = True
isStrong (_ :< NeutHole _) = False
isStrong (_ :< NeutSubst (_ :< NeutHole x) sub) =
  case lookup x sub of
    Nothing -> False
    Just e  -> isStrong e
isStrong e@(_ :< NeutSubst _ _) = isStrong $ reduce e

substEq :: Subst -> Equation -> Equation
substEq sub (EquationPiElim t1 e2 hole) = do
  let t1' = subst sub t1
  let e2' = subst sub e2
  EquationPiElim t1' e2' hole
substEq sub (EquationSigmaElim e1 (t2, (x, y)) hole) = do
  let e1' = subst sub e1
  let t2' = subst sub t2
  EquationSigmaElim e1' (t2', (x, y)) hole

unifyEq :: [Equation] -> WithEnv ([Equation], Subst)
unifyEq [] = return ([], [])
unifyEq (eq@(EquationPiElim t1 _ _):rest)
  | not (isStrong t1) = do
    (eqs, s) <- unifyEq rest
    return (eq : eqs, s)
unifyEq (EquationPiElim (_ :< NeutPi (x, _) tcod) e2 hole:rest) = do
  let t2' = subst [(x, e2)] tcod
  (eqs, s) <- unifyEq rest
  return (eqs, (hole, t2') : s)
unifyEq (EquationPiElim t _ _:_) =
  lift $
  throwE $
  "the type " ++ Pr.ppShow t ++ " is expected to be a pi-type, but not."
unifyEq (eq@(EquationSigmaElim _ (t2, _) _):rest)
  | not (isStrong t2) = do
    (eqs, s) <- unifyEq rest
    return (eq : eqs, s)
unifyEq (EquationSigmaElim e1 (t2, (x, y)) hole:rest) = do
  let t2' = substPair (x, y) e1 t2
  (eqs, s) <- unifyEq rest
  return (eqs, (hole, t2') : s)

substPair :: (Identifier, Identifier) -> Neut -> Neut -> Neut
substPair _ _ e@(_ :< NeutVar _) = e
substPair (x, y) dest (meta :< NeutPi (z, tdom) tcod) = do
  let tdom' = substPair (x, y) dest tdom
  let tcod' = substPair (x, y) dest tcod
  meta :< NeutPi (z, tdom') tcod'
substPair (x, y) dest (meta :< NeutPiIntro (z, tdom) body) = do
  let tdom' = substPair (x, y) dest tdom
  let body' = substPair (x, y) dest body
  meta :< NeutPiIntro (z, tdom') body'
substPair (x, y) dest (meta :< NeutPiElim e1 e2) = do
  let e1' = substPair (x, y) dest e1
  let e2' = substPair (x, y) dest e2
  meta :< NeutPiElim e1' e2'
substPair (x, y) dest (meta :< NeutSigma (z, tl) tr) = do
  let tl' = substPair (x, y) dest tl
  let tr' = substPair (x, y) dest tr
  meta :< NeutSigma (z, tl') tr'
substPair (x, y) dest (_ :< NeutSigmaIntro (_ :< NeutVar p) (_ :< NeutVar q))
  | p == x && q == y = dest
substPair (x, y) dest (meta :< NeutSigmaIntro e1 e2) = do
  let e1' = substPair (x, y) dest e1
  let e2' = substPair (x, y) dest e2
  meta :< NeutSigmaIntro e1' e2'
substPair (x, y) dest (meta :< NeutSigmaElim e1 (p, q) e2) = do
  let e1' = substPair (x, y) dest e1
  let e2' = substPair (x, y) dest e2
  meta :< NeutSigmaElim e1' (p, q) e2'
substPair (x, y) dest (meta :< NeutMu z e) = do
  let e' = substPair (x, y) dest e
  meta :< NeutMu z e'
substPair _ _ e@(_ :< NeutTop) = e
substPair _ _ e@(_ :< NeutTopIntro) = e
substPair _ _ e@(_ :< NeutIndex _) = e
substPair _ _ e@(_ :< NeutIndexIntro _) = e
substPair (x, y) dest (meta :< NeutIndexElim e branchList) = do
  let e' = substPair (x, y) dest e
  let (labelList, es) = unzip branchList
  let es' = map (substPair (x, y) dest) es
  meta :< NeutIndexElim e' (zip labelList es')
substPair _ _ e@(_ :< NeutUniv _) = e
substPair _ _ e@(_ :< NeutHole _) = e -- shouldn't occur
substPair (x, y) dest (_ :< NeutSubst (meta :< NeutHole z) sub) =
  case lookup z sub of
    Nothing -> meta :< NeutHole x
    Just e  -> substPair (x, y) dest e
substPair (x, y) dest e@(_ :< NeutSubst _ _) = substPair (x, y) dest $ reduce e
