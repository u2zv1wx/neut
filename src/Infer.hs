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
import           Data.List
import           Data.Maybe

check :: Identifier -> Neut -> WithEnv Neut
check main e = do
  t <- infer [] e
  insTypeEnv main t -- insert the type of main function
  affineConstraint' [] e
  env <- get
  liftIO $ putStrLn $ "constraint = " ++ Pr.ppShow (constraintEnv env)
  sub <- unifyLoop (constraintEnv env) 0
  let (is, ts) = unzip $ typeEnv env
  let ts' = map (subst sub) ts
  let tenv' = zip is ts'
  modify (\e -> e {typeEnv = tenv', constraintEnv = []})
  return $ subst sub e

infer :: Context -> Neut -> WithEnv Neut
infer _ (meta :< NeutVar s) = do
  t <- lookupTypeEnv' s
  returnMeta meta t
infer ctx (meta :< NeutPi (s, tdom) tcod) = inferBinder ctx meta s tdom tcod
infer ctx (meta :< NeutPiIntro (s, tdom) e) = do
  let ctx' = ctx ++ [s]
  insTypeEnv s tdom
  udom <- infer ctx' tdom
  (tcod, ucod) <- infer2 ctx' e
  insConstraintEnv ctx udom ucod
  wrapTypeWithUniv udom (NeutPi (s, tdom) tcod) >>= returnMeta meta
infer ctx (meta :< NeutPiElim e1 e2) = do
  tPi <- infer ctx e1 -- forall (x : tdom). tcod
  (tdom, udom) <- infer2 ctx e2
  codName <- newName
  x <- newNameOfType tdom
  typeMeta2 <- newNameWith "meta"
  insTypeEnv typeMeta2 udom
  tcod <- wrapType (NeutHole codName) >>= appCtx (ctx ++ [x])
  ucod <- infer (ctx ++ [x]) tcod
  insConstraintEnv ctx udom ucod
  insConstraintEnv ctx tPi (typeMeta2 :< NeutPi (x, tdom) tcod) -- t1 == forall (x : tdom). tcod
  returnMeta meta $ subst [(x, e2)] tcod
infer ctx (meta :< NeutSigma (s, tdom) tcod) = inferBinder ctx meta s tdom tcod
infer ctx (meta :< NeutSigmaIntro e1 e2) = do
  (t1, u1) <- infer2 ctx e1
  (t2, u2) <- infer2 ctx e2
  insConstraintEnv ctx u1 u2
  x <- newNameOfType t1
  typeB <- newHole >>= appCtx (ctx ++ [x]) -- B
  insConstraintEnv ctx t2 $ subst [(x, e1)] typeB
  wrapTypeWithUniv u1 (NeutSigma (x, t1) typeB) >>= returnMeta meta -- Sigma (x : A). B
infer ctx (meta :< NeutSigmaElim e1 (x, y) e2) = do
  (t1, u1) <- infer2 ctx e1
  tx <- newHole >>= appCtx ctx
  ux <- infer ctx tx
  insTypeEnv x tx
  ty <- newHole >>= appCtx (ctx ++ [x])
  uy <- infer ctx ty
  insTypeEnv y ty
  (t2, u2) <- infer2 (ctx ++ [x, y]) e2
  insConstraintEnv ctx u1 u2
  insConstraintEnv ctx u1 ux
  insConstraintEnv ctx ux uy
  sigmaType <- wrapType $ NeutSigma (x, tx) ty
  insConstraintEnv ctx t1 sigmaType
  z <- newNameOfType t1
  pair <- constructPair (ctx ++ [x, y]) x y
  typeC <- newHole >>= appCtx (ctx ++ [x, y, z])
  insConstraintEnv ctx t2 $ subst [(z, pair)] typeC
  returnMeta meta $ subst [(z, e1)] typeC
infer ctx (meta :< NeutBox t) = do
  u <- infer ctx t
  returnMeta meta u
infer ctx (meta :< NeutBoxIntro e) = do
  t <- infer ctx e
  affineConstraint ctx e
  u <- infer ctx t
  wrapTypeWithUniv u (NeutBox t) >>= returnMeta meta
infer ctx (meta :< NeutBoxElim e) = do
  t <- infer ctx e
  resultHole <- newHole >>= appCtx ctx
  boxType <- wrapType $ NeutBox resultHole
  insConstraintEnv ctx t boxType
  returnMeta meta resultHole
infer ctx (meta :< NeutMu s e) = do
  trec <- newHole
  insTypeEnv s trec
  te <- infer (ctx ++ [s]) e
  insConstraintEnv ctx te trec
  returnMeta meta te
infer _ (meta :< NeutIndex _) = do
  hole <- newName
  wrap (NeutUniv (UnivLevelHole hole)) >>= returnMeta meta
infer _ (meta :< NeutIndexIntro l) = do
  mk <- lookupKind l
  case mk of
    Just k -> do
      t <- wrapType $ NeutIndex k
      returnMeta meta t
    Nothing -> undefined -- shouldn't occur
infer _ (_ :< NeutIndexElim _ []) = lift $ throwE "empty branch"
infer ctx (meta :< NeutIndexElim e branchList) = do
  t <- infer ctx e
  let (labelList, es) = unzip branchList
  tls <- mapM inferIndex labelList
  let tls' = join $ map maybeToList tls
  constrainList ctx tls'
  headConstraint ctx t tls'
  tes <- mapM (infer ctx) es
  constrainList ctx tes
  returnMeta meta $ head tes
infer _ (meta :< NeutUniv l) =
  wrap (NeutUniv (UnivLevelNext l)) >>= returnMeta meta
infer ctx (meta :< NeutHole _) = do
  hole <- newHole >>= appCtx ctx
  returnMeta meta hole

infer2 :: Context -> Neut -> WithEnv (Neut, Neut)
infer2 ctx e = do
  t <- infer ctx e
  u <- infer ctx t
  return (t, u)

inferIndex :: Index -> WithEnv (Maybe Neut)
inferIndex name = do
  mk <- lookupKind name
  case mk of
    Just k  -> Just <$> wrapType (NeutIndex k)
    Nothing -> return Nothing

constrainList :: Context -> [Neut] -> WithEnv ()
constrainList _ [] = return ()
constrainList _ [_] = return ()
constrainList ctx (t1:t2:ts) = do
  insConstraintEnv ctx t1 t2
  constrainList ctx $ t2 : ts

headConstraint :: Context -> Neut -> [Neut] -> WithEnv ()
headConstraint _ _ []        = return ()
headConstraint ctx t1 (t2:_) = insConstraintEnv ctx t1 t2

inferBinder ::
     Context -> Identifier -> Identifier -> Neut -> Neut -> WithEnv Neut
inferBinder ctx meta s tdom tcod = do
  udom <- infer ctx tdom
  insTypeEnv s tdom
  ucod <- infer (ctx ++ [s]) tcod
  insConstraintEnv ctx udom ucod
  returnMeta meta udom

constructPair :: Context -> Identifier -> Identifier -> WithEnv Neut
constructPair ctx x y = do
  eMeta <- newName
  xMeta <- newName
  yMeta <- newName
  let pair = eMeta :< NeutSigmaIntro (xMeta :< NeutVar x) (yMeta :< NeutVar y)
  _ <- infer ctx pair
  return pair

newNameOfType :: Neut -> WithEnv Identifier
newNameOfType t = do
  i <- newName
  insTypeEnv i t
  return i

-- apply all the context variables to e
appCtx :: Context -> Neut -> WithEnv Neut
appCtx [] e = return e
appCtx ctx@(x:xs) e = do
  txs <- mapM lookupTypeEnv' xs
  uxs <- mapM (infer ctx) txs
  univ <- newName >>= \x -> wrap (NeutUniv (UnivLevelHole x))
  arrowType <- foldMR NeutPi univ $ zip xs txs
  te <- infer ctx e
  insConstraintEnv ctx te arrowType
  constrainList ctx $ univ : uxs
  varMeta <- newName
  tx <- lookupTypeEnv' x
  insTypeEnv varMeta tx
  let var = varMeta :< NeutVar x
  appMeta <- newName
  arrowType' <- foldMR NeutPi univ $ drop 1 $ zip xs txs
  insTypeEnv appMeta arrowType'
  let app = appMeta :< NeutPiElim e var
  appCtx xs app

newHole :: WithEnv Neut
newHole = do
  i <- newName
  wrapType $ NeutHole i

returnMeta :: Identifier -> Neut -> WithEnv Neut
returnMeta meta t = do
  insTypeEnv meta t
  return t

unifyLoop :: Constraint -> Int -> WithEnv Subst
unifyLoop [] _ = return []
unifyLoop ((ctx, (e1, e2)):cs) loopCount = do
  e1' <- reduce e1
  e2' <- reduce e2
  (s, tmpConstraint) <- unify ((ctx, (e1', e2')) : cs)
  liftIO $ putStrLn $ "subst:\n " ++ Pr.ppShow s
  case tmpConstraint of
    [] -> return s
    (ctx', (e1'', e2'')):cs' -> do
      let loopCount' = nextLoopCount (length cs) (length cs') loopCount
      if didFinishLoop (length cs') loopCount'
        then do
          liftIO $ putStrLn $ "failing unification. subst:\n" ++ Pr.ppShow s
          unificationFailed e1'' e2'' cs'
        else do
          s' <- unifyLoop (cs' ++ [(ctx', (e1'', e2''))]) loopCount'
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
unify ((ctx, (_ :< NeutHole s, t2)):cs) = do
  liftIO $ putStrLn $ "found a substition:\n" ++ Pr.ppShow (s, t2)
  cs' <- sConstraint [(s, t2)] cs
  (sub, cs'') <- unify cs'
  let sub' = compose sub [(s, t2)]
  return (sub', cs'')
unify ((ctx, (t1, _ :< NeutHole s)):cs) = do
  liftIO $ putStrLn $ "found a substition:\n" ++ Pr.ppShow (s, t1)
  cs' <- sConstraint [(s, t1)] cs
  (sub, cs'') <- unify cs'
  let sub' = compose sub [(s, t1)]
  return (sub', cs'')
unify ((ctx, (_ :< NeutVar s1, _ :< NeutVar s2)):cs)
  | s1 == s2 = unify cs
unify ((ctx, (_ :< NeutPi (x, tdom1) tcod1, _ :< NeutPi (y, tdom2) tcod2)):cs) = do
  z <- newName
  insTypeEnv z tdom1
  meta <- newName
  insTypeEnv meta tdom1
  let var = meta :< NeutVar z
  unify $
    (ctx, (tdom1, tdom2)) :
    (ctx ++ [z], (subst [(x, var)] tcod1, subst [(y, var)] tcod2)) : cs
unify ((ctx, (_ :< NeutPiIntro (x, tdom1) body1, _ :< NeutPiIntro (y, tdom2) body2)):cs) = do
  z <- newName
  insTypeEnv z tdom1
  meta <- newName
  insTypeEnv meta tdom1
  let var = meta :< NeutVar z
  -- unify $ (tdom1, tdom2) : (subst [(x, var)] body1, subst [(y, var)] body2) : cs
  unify $
    (ctx, (tdom1, tdom2)) :
    (ctx ++ [z], (subst [(x, var)] body1, subst [(y, var)] body2)) : cs
unify ((ctx, (_ :< NeutPiIntro (x, tdom1) body1, e2)):cs) = do
  undefined
unify ((ctx, (e1, _ :< NeutPiIntro (y, tdom2) body2)):cs) = do
  undefined
unify ((ctx, (_ :< NeutSigma (x, tdom1) tcod1, _ :< NeutSigma (y, tdom2) tcod2)):cs) = do
  z <- newName
  insTypeEnv z tdom1
  meta <- newName
  insTypeEnv meta tdom1
  let var = meta :< NeutVar z
  unify $
    (ctx, (tdom1, tdom2)) :
    (ctx ++ [z], (subst [(x, var)] tcod1, subst [(y, var)] tcod2)) : cs
unify ((ctx, (_ :< NeutSigmaIntro e11 e12, _ :< NeutSigmaIntro e21 e22)):cs) = do
  undefined
unify ((ctx, (_ :< NeutSigmaIntro e11 e12, e2)):cs) = do
  undefined
unify ((ctx, (e1, _ :< NeutSigmaIntro e21 e22)):cs) = do
  undefined
unify ((ctx, (_ :< NeutBox t1, _ :< NeutBox t2)):cs) =
  unify $ (ctx, (t1, t2)) : cs
unify ((ctx, (_ :< NeutIndex l1, _ :< NeutIndex l2)):cs)
  | l1 == l2 = unify cs
unify ((ctx, (_ :< NeutUniv i, _ :< NeutUniv j)):cs) = do
  insUnivConstraintEnv i j
  unify cs
unify cs = return ([], cs)

sConstraint :: Subst -> Constraint -> WithEnv Constraint
sConstraint s ctcs = do
  let (ctxList, cs) = unzip ctcs
  let (ts1, ts2) = unzip cs
  let ts1' = map (subst s) ts1
  let ts2' = map (subst s) ts2
  return $ zip ctxList $ zip ts1' ts2'

occursMoreThanTwice :: Eq a => [a] -> [a]
occursMoreThanTwice xs = do
  let ys = nub xs
  nub $ occursMoreThanTwice' ys xs

occursMoreThanTwice' :: Eq a => [a] -> [a] -> [a]
occursMoreThanTwice' ys xs = foldl (flip delete) xs ys

affineConstraint :: Context -> Neut -> WithEnv ()
affineConstraint ctx e = do
  varList <- var e
  affineConstraint0 ctx $ nub varList

affineConstraint' :: Context -> Neut -> WithEnv ()
affineConstraint' ctx e = do
  varList <- var' e
  let xs = occursMoreThanTwice varList
  affineConstraint0 ctx xs

affineConstraint0 :: Context -> [Identifier] -> WithEnv ()
affineConstraint0 ctx xs =
  forM_ xs $ \x -> do
    t <- lookupTypeEnv' x
    h <- newHole
    boxType <- wrapType $ NeutBox h
    insConstraintEnv ctx t boxType
