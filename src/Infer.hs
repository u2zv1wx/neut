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
import           Reduce
import           Util

import           Data.List

import           Data.Maybe

check :: Identifier -> Neut -> WithEnv Neut
check main e = do
  t <- infer [] e
  insTypeEnv main t -- insert the type of main function
  boxConstraint [] $ nonLinear e
  liftIO $ putStrLn $ "unification start"
  env <- get
  sub <- unifyLoop (constraintEnv env) 0
  let tenv' = map (\(i, t) -> (i, subst sub t)) $ typeEnv env
  modify (\e -> e {typeEnv = tenv'})
  checkNumConstraint
  return $ subst sub e

infer :: Context -> Neut -> WithEnv Neut
infer _ (meta :< NeutVar s) = do
  t <- lookupTypeEnv' s
  returnMeta meta t
infer _ (meta :< NeutConst s) = do
  t <- lookupConstEnv' s
  returnMeta meta t
infer ctx (meta :< NeutPi (s, tdom) tcod) =
  inferBinder ctx s tdom tcod >>= returnMeta meta
infer ctx (meta :< NeutPiIntro (s, tdom) e) = do
  insTypeEnv s tdom
  higherUniv <- boxUniv
  udom <- infer ctx tdom >>= annot higherUniv
  let ctx' = ctx ++ [s]
  tcod <- infer ctx' e
  ucod <- infer ctx' tcod >>= annot higherUniv
  insConstraintEnv ctx' udom ucod higherUniv
  typeMeta <- newNameWith "meta"
  insTypeEnv typeMeta udom
  returnMeta meta $ typeMeta :< NeutPi (s, tdom) tcod
infer ctx (meta :< NeutPiElim e1 e2) = do
  tPi <- infer ctx e1 -- forall (x : tdom). tcod
  -- declare the universe of tdom, tcod
  higherUniv <- boxUniv
  -- infer the type of e2, and obtain (tdom, udom)
  tdom <- infer ctx e2
  udom <- infer ctx tdom >>= annot higherUniv
  -- represent (tcod, ucod) using hole
  x <- newNameOfType tdom
  ucod <- boxUniv >>= annot higherUniv
  tcod <- appCtx (ctx ++ [x]) >>= annot ucod
  -- add a constraint regarding the level of universes
  insConstraintEnv ctx udom ucod higherUniv
  -- add a constraint regarding the Pi-type
  typeMeta <- newNameWith "meta"
  insTypeEnv typeMeta udom
  insConstraintEnv ctx tPi (typeMeta :< NeutPi (x, tdom) tcod) udom
  -- return the type of this elimination
  returnMeta meta $ subst [(x, e2)] tcod
infer _ (_ :< NeutSigma [] _) =
  lift $ throwE "Infer.Sigma: Sigma without arguments"
infer ctx (meta :< NeutSigma [(s, tdom)] tcod) =
  inferBinder ctx s tdom tcod >>= returnMeta meta
infer ctx (_ :< NeutSigma ((s, tdom):xts) tcod) = do
  udom <- infer ctx tdom
  insTypeEnv s tdom
  meta <- newNameWith "meta"
  ucod <- infer (ctx ++ [s]) (meta :< NeutSigma xts tcod)
  u <- boxUniv
  insConstraintEnv ctx udom ucod u
  return udom
infer _ (_ :< NeutSigmaIntro []) = undefined
infer _ (_ :< NeutSigmaIntro [_]) = undefined
infer ctx (meta :< NeutSigmaIntro es) = do
  tus <- mapM (infer2 ctx) es
  let (ts, us) = unzip tus
  constrainList ctx us
  xs <- forM ts newNameOfType
  holeList <- sigmaHole ctx xs
  let xes = zip xs es
  let holeList' = map (subst xes) holeList
  forM_ (zip holeList' ts) $ \(h, t) -> insConstraintEnv ctx h t (head us)
  let binder = zip xs (take (length holeList - 1) holeList)
  wrapTypeWithUniv (head us) (NeutSigma binder (last holeList)) >>=
    returnMeta meta
infer ctx (meta :< NeutSigmaElim e1 xs e2) = do
  (t1, u1) <- infer2 ctx e1
  holeList <- sigmaHole ctx xs
  forM_ (zip xs holeList) $ uncurry insTypeEnv
  (t2, u2) <- infer2 (ctx ++ xs) e2
  let binder = zip xs (take (length holeList - 1) holeList)
  let cod = last holeList
  sigmaType <- wrapType $ NeutSigma binder cod
  insConstraintEnv ctx t1 sigmaType u1
  z <- newNameOfType t1
  pair <- constructPair (ctx ++ xs) xs
  typeC <- appCtx (ctx ++ xs ++ [z])
  insConstraintEnv ctx t2 (subst [(z, pair)] typeC) u2
  returnMeta meta $ subst [(z, e1)] typeC
infer ctx (meta :< NeutBox t) = do
  higherUniv <- boxUniv
  u <- infer ctx t >>= annot higherUniv
  bu <- boxUniv >>= annot higherUniv
  insConstraintEnv ctx u bu higherUniv
  returnMeta meta u
infer ctx (meta :< NeutBoxIntro e) = do
  t <- infer ctx e
  boxConstraint ctx $ var e
  u <- infer ctx t
  wrapTypeWithUniv u (NeutBox t) >>= returnMeta meta
infer ctx (meta :< NeutBoxElim e) = do
  t <- infer ctx e
  resultHole <- appCtx ctx
  boxType <- wrapType $ NeutBox resultHole
  u <- infer ctx t
  insConstraintEnv ctx t boxType u
  returnMeta meta resultHole
infer _ (meta :< NeutIndex _) = boxUniv >>= returnMeta meta
infer ctx (meta :< NeutIndexIntro l) = do
  mk <- lookupKind l
  case mk of
    Just k -> do
      t <- wrapType $ NeutIndex k
      returnMeta meta t
    Nothing -> do
      hole <- appCtx ctx
      liftIO $
        putStrLn $
        "add num constraint for: " ++ Pr.ppShow (meta :< NeutIndexIntro l)
      insNumConstraintEnv meta
      returnMeta meta hole
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
infer ctx (meta :< NeutMu s e) = do
  trec <- appCtx ctx
  insTypeEnv s trec
  te <- infer (ctx ++ [s]) e
  u <- infer (ctx ++ [s]) te
  insConstraintEnv ctx te trec u
  returnMeta meta te
infer _ (meta :< NeutUniv _) = boxUniv >>= returnMeta meta
infer ctx (meta :< NeutHole _) = appCtx ctx >>= returnMeta meta

infer2 :: Context -> Neut -> WithEnv (Neut, Neut)
infer2 ctx e = do
  t <- infer ctx e
  u <- infer ctx t
  return (t, u)

sigmaHole :: Context -> [Identifier] -> WithEnv [Neut]
sigmaHole ctx xs = forM (zip xs [0 ..]) $ \(_, i) -> sigmaHole' ctx xs i

sigmaHole' :: Context -> [Identifier] -> Int -> WithEnv Neut
sigmaHole' ctx xs i = appCtx (ctx ++ take i xs)

inferIndex :: Index -> WithEnv (Maybe Neut)
inferIndex name = do
  mk <- lookupKind name
  case mk of
    Just k  -> Just <$> wrapType (NeutIndex k)
    Nothing -> return Nothing

constrainList :: Context -> [Neut] -> WithEnv ()
constrainList _ [] = return ()
constrainList _ [_] = return ()
constrainList ctx (t1@(meta1 :< _):t2@(meta2 :< _):ts) = do
  u <- boxUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  insConstraintEnv ctx t1 t2 u
  constrainList ctx $ t2 : ts

headConstraint :: Context -> Neut -> [Neut] -> WithEnv ()
headConstraint _ _ [] = return ()
headConstraint ctx t1@(meta1 :< _) (t2@(meta2 :< _):_) = do
  u <- boxUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  insConstraintEnv ctx t1 t2 u

inferBinder :: Context -> Identifier -> Neut -> Neut -> WithEnv Neut
inferBinder ctx s tdom tcod = do
  insTypeEnv s tdom
  higherUniv <- boxUniv
  udom <- infer ctx tdom >>= annot higherUniv
  ucod <- infer (ctx ++ [s]) tcod >>= annot higherUniv
  ub <- boxUniv >>= annot higherUniv
  insConstraintEnv (ctx ++ [s]) udom ub higherUniv
  insConstraintEnv (ctx ++ [s]) udom ucod higherUniv
  return udom

annot :: Neut -> Neut -> WithEnv Neut
annot t e@(meta :< _) = insTypeEnv meta t >> return e

constructPair :: Context -> [Identifier] -> WithEnv Neut
constructPair ctx xs = do
  eMeta <- newName
  metaList <- mapM (const newName) xs
  let varList = map (\(m, x) -> m :< NeutVar x) $ zip metaList xs
  let pair = eMeta :< NeutSigmaIntro varList
  _ <- infer ctx pair
  return pair

newNameOfType :: Neut -> WithEnv Identifier
newNameOfType t = do
  i <- newName
  insTypeEnv i t
  return i

newName' :: Identifier -> Neut -> WithEnv Identifier
newName' name t = do
  i <- newNameWith name
  insTypeEnv i t
  return i

-- apply all the context variables to e
appCtx :: Context -> WithEnv Neut
appCtx ctx = do
  tctxs <- mapM lookupTypeEnv' ctx
  univ <- boxUniv
  higherArrowType <- foldMR NeutPi univ $ zip ctx tctxs
  higherHoleName <- newName' "ctx" higherArrowType
  higherMeta <- newName' "ctx" higherArrowType
  insTypeEnv higherMeta higherArrowType
  let higherHole = higherMeta :< NeutHole higherHoleName
  varSeq <- mapM toVar ctx
  cod <- appFold higherHole varSeq
  arrowType <- foldMR NeutPi cod $ zip ctx tctxs
  holeName <- newName' "hole" arrowType
  meta <- newName' "meta" arrowType
  appFold (meta :< NeutHole holeName) varSeq

toVar :: Identifier -> WithEnv Neut
toVar x = do
  t <- lookupTypeEnv' x
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutVar x

returnMeta :: Identifier -> Neut -> WithEnv Neut
returnMeta meta t = do
  insTypeEnv meta t
  return t

unifyLoop :: Constraint -> Int -> WithEnv Subst
unifyLoop [] _ = return []
unifyLoop ((ctx, e1, e2, t):cs) loopCount = do
  e1' <- reduce e1
  e2' <- reduce e2
  (s, tmpConstraint) <- unify ((ctx, e1', e2', t) : cs)
  -- liftIO $ putStrLn $ "subst:\n" ++ Pr.ppShow s
  case tmpConstraint of
    [] -> return s
    (ctx', e1'', e2'', t'):cs' -> do
      let loopCount' = nextLoopCount (length cs) (length cs') loopCount
      if didFinishLoop (length cs') loopCount'
        then do
          liftIO $ putStrLn $ "failing unification. subst:\n" ++ Pr.ppShow s
          liftIO $ putStrLn $ "ctx:\n" ++ Pr.ppShow ctx'
          unificationFailed e1'' e2'' cs'
        else do
          s' <- unifyLoop (cs' ++ [(ctx', e1'', e2'', t')]) loopCount'
          return (s ++ s')

unificationFailed :: Neut -> Neut -> Constraint -> WithEnv Subst
unificationFailed e1 e2 cs = do
  liftIO $ putStrLn $ "constraints:\n" ++ Pr.ppShow cs
  lift $
    throwE $
    "unification failed for\n" ++ Pr.ppShow e1 ++ "\nand\n" ++ Pr.ppShow e2

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
unify ((_, _ :< NeutVar s1, _ :< NeutVar s2, _):cs)
  | s1 == s2 = unify cs
unify ((ctx, _ :< NeutPi (x, tdom1) tcod1, _ :< NeutPi (y, tdom2) tcod2, univ):cs) =
  unifyBinder ctx ((x, tdom1), tcod1) ((y, tdom2), tcod2) univ cs
unify ((ctx, _ :< NeutPiIntro (x, tdom1@(meta1 :< _)) body1, _ :< NeutPiIntro (y, tdom2@(meta2 :< _)) body2, _ :< NeutPi (z, tdom) tcod):cs) = do
  meta <- newName
  insTypeEnv meta tdom
  let var = meta :< NeutVar z
  u <- boxUniv
  insTypeEnv meta1 u
  insTypeEnv meta2 u
  let foo =
        [ (ctx, tdom1, tdom2, u)
        , (ctx ++ [z], subst [(x, var)] body1, subst [(y, var)] body2, tcod)
        ]
  liftIO $ putStrLn $ "new constraints:\n" ++ Pr.ppShow foo
  unify $
    (ctx, tdom1, tdom2, u) :
    (ctx ++ [z], subst [(x, var)] body1, subst [(y, var)] body2, tcod) : cs
unify ((ctx, _ :< NeutPiIntro (x, tdom1) body1, e2, _ :< NeutPi (z, _) tcod):cs) = do
  c <- constraintPiElim ctx ((x, tdom1), body1) e2 z tcod
  unify $ c : cs
unify ((ctx, e1, _ :< NeutPiIntro (y, tdom2) body2, _ :< NeutPi (z, _) tcod):cs) = do
  c <- constraintPiElim ctx ((y, tdom2), body2) e1 z tcod
  unify $ c : cs
unify ((ctx, _ :< NeutSigma [(x, tdom1)] tcod1, _ :< NeutSigma [(y, tdom2)] tcod2, univ):cs) =
  unifyBinder ctx ((x, tdom1), tcod1) ((y, tdom2), tcod2) univ cs
unify ((ctx, i :< NeutSigma ((x, tdom1):xts) tcod1, j :< NeutSigma ((y, tdom2):yts) tcod2, univ):cs) = do
  let sig1 = i :< NeutSigma [(x, tdom1)] (i :< NeutSigma xts tcod1)
  let sig2 = j :< NeutSigma [(y, tdom2)] (j :< NeutSigma yts tcod2)
  unify ((ctx, sig1, sig2, univ) : cs)
unify ((ctx, _ :< NeutSigmaIntro es1, _ :< NeutSigmaIntro es2, _ :< NeutSigma xts t):cs)
  | length es1 == length es2 = do
    let ts = map snd xts ++ [t]
    let sub = zip (map fst xts) es1
    let ts' = map (subst sub) ts
    newCs <-
      forM (zip (zip es1 es2) ts') $ \((e1, e2), t') -> return (ctx, e1, e2, t')
    unify $ newCs ++ cs
unify ((ctx, _ :< NeutSigmaIntro es, e2, _ :< NeutSigma xts t):cs)
  | length xts + 1 == length es = unifySigma ctx e2 es xts t cs
unify ((ctx, e1, _ :< NeutSigmaIntro es, _ :< NeutSigma xts t):cs)
  | length xts + 1 == length es = unifySigma ctx e1 es xts t cs
unify ((ctx, _ :< NeutBox t1, _ :< NeutBox t2, univ):cs) =
  unify $ (ctx, t1, t2, univ) : cs
unify ((ctx, _ :< NeutBoxIntro e1, _ :< NeutBoxIntro e2, _ :< NeutBox t):cs) =
  unify $ (ctx, e1, e2, t) : cs
unify ((_, _ :< NeutIndex l1, _ :< NeutIndex l2, _):cs)
  | l1 == l2 = unify cs
unify ((_, _ :< NeutUniv i, _ :< NeutUniv j, _):cs) = do
  insUnivConstraintEnv i j
  unify cs
unify (c@(_, e1, e2, _):cs)
  | Just (x, args) <- headMeta [] e1 = do
    liftIO $ putStrLn $ "trying:\n" ++ Pr.ppShow c
    let (fvs, fmvs) = varAndHole e2
    if affineCheck args fvs && x `notElem` fmvs
      then do
        liftIO $ putStrLn $ "resolving:\n" ++ Pr.ppShow c
        ans <- bindFormalArgs args e2
        -- liftIO $ putStrLn $ "sub:\n" ++ Pr.ppShow (x, ans)
        cs' <- sConstraint [(x, ans)] cs
        (sub, cs'') <- unify cs'
        let sub' = compose sub [(x, ans)]
        return (sub', cs'')
      else do
        liftIO $ putStrLn "affineCheck failed"
        return ([], c : cs)
unify ((ctx, e1, e2, t):cs)
  | Just _ <- headMeta [] e2 = unify $ (ctx, e2, e1, t) : cs
unify cs = return ([], cs)

unifySigma ctx e es xts t cs = do
  prList <- projectionList e (xts, t)
  let sub = zip (map fst xts) es
  let ts = map (subst sub) $ map snd xts ++ [t]
  newCs <-
    forM (zip3 es prList ts) $ \(e, ithProj, t) -> return (ctx, e, ithProj, t)
  unify $ newCs ++ cs

headMeta :: [Identifier] -> Neut -> Maybe (Identifier, [Identifier])
headMeta args (_ :< NeutPiElim e1 (_ :< NeutVar x)) = headMeta (x : args) e1
headMeta args (_ :< NeutHole x)                     = Just (x, args)
headMeta _ _                                        = Nothing

affineCheck :: [Identifier] -> [Identifier] -> Bool
affineCheck xs = affineCheck' xs xs

affineCheck' :: [Identifier] -> [Identifier] -> [Identifier] -> Bool
affineCheck' _ [] _ = True
affineCheck' xs (y:ys) fvs =
  if y `notElem` fvs
    then affineCheck' xs ys fvs
    else null (isLinear y xs) && affineCheck' xs ys fvs

projectionList :: Neut -> ([(Identifier, Neut)], Neut) -> WithEnv [Neut]
projectionList e (xts, t) = do
  xiList <- forM (map snd xts ++ [t]) $ \t -> newNameOfType t
  metaList <- mapM (const newName) xiList
  let varList = map (\(m, x) -> m :< NeutVar x) $ zip metaList xiList
  forM varList $ \v -> do
    meta <- newName
    return $ meta :< NeutSigmaElim e xiList v

unifyBinder ctx ((x, tdom1@(tdomMeta1 :< _)), tcod1@(tcodMeta1 :< _)) ((y, tdom2@(tdomMeta2 :< _)), tcod2@(tcodMeta2 :< _)) univ cs = do
  z <- newName
  insTypeEnv z tdom1
  u <- boxUniv
  insTypeEnv tdomMeta1 u
  insTypeEnv tcodMeta1 u
  insTypeEnv tdomMeta2 u
  insTypeEnv tcodMeta2 u
  meta <- newName
  insTypeEnv meta tdom1
  let var = meta :< NeutVar z
  liftIO $
    putStrLn $
    "UnifyBinder. x == " ++ show x ++ ", y == " ++ show y ++ ", z == " ++ show z
  -- ctx' <- sConstraint [(x, var), (y, var)] ctx
  let ctx' = map (\w -> fromMaybe w (lookup w [(x, z), (y, z)])) ctx
  let univ' = subst [(x, var), (y, var)] univ
  cs' <- sConstraint [(x, var), (y, var)] cs
  unify $
    (ctx', tdom1, tdom2, univ') :
    (ctx' ++ [z], subst [(x, var)] tcod1, subst [(y, var)] tcod2, univ') : cs'

constraintPiElim ctx ((x, tdom), body) e2 z tcod = do
  liftIO $ putStrLn $ "piElim. x = " ++ x
  meta <- newName
  varX <- toVar x
  let tcod' = subst [(z, varX)] tcod
  insTypeEnv meta tcod'
  varMeta <- newName
  insTypeEnv varMeta tdom
  let var = varMeta :< NeutVar x
  appMeta <- newName
  insTypeEnv appMeta tcod'
  let app = appMeta :< NeutPiElim e2 var
  let foo = (ctx ++ [x], body, app, tcod')
  liftIO $ putStrLn $ "new constraints:\n" ++ Pr.ppShow foo
  return (ctx ++ [x], body, app, tcod')

sConstraint :: Subst -> Constraint -> WithEnv Constraint
sConstraint s ctcs = do
  let (ctxList, cs, typeList) = split ctcs
  let (ts1, ts2) = unzip cs
  let ts1' = map (subst s) ts1
  let ts2' = map (subst s) ts2
  let typeList' = map (subst s) typeList
  return $ unsplit ctxList (zip ts1' ts2') typeList'

split :: Constraint -> ([[Identifier]], [(Neut, Neut)], [Neut])
split [] = ([], [], [])
split ((ctx, e1, e2, t):rest) = do
  let (ctxList, cs, typeList) = split rest
  (ctx : ctxList, (e1, e2) : cs, t : typeList)

unsplit :: [[Identifier]] -> [(Neut, Neut)] -> [Neut] -> Constraint
unsplit [] [] [] = []
unsplit (ctx:ctxList) ((e1, e2):cs) (t:typeList) =
  (ctx, e1, e2, t) : unsplit ctxList cs typeList
unsplit _ _ _ = error "Infer.unsplit: invalid arguments"

boxConstraint :: Context -> [Identifier] -> WithEnv ()
boxConstraint ctx xs =
  forM_ xs $ \x -> do
    t <- lookupTypeEnv' x
    h <- appCtx ctx
    boxType@(meta :< _) <- wrapType $ NeutBox h
    u <- lookupTypeEnv' meta
    insConstraintEnv ctx t boxType u

checkNumConstraint :: WithEnv ()
checkNumConstraint = do
  env <- get
  forM_ (numConstraintEnv env) $ \x -> do
    t <- lookupTypeEnv' x
    t' <- reduce t
    case t' of
      _ :< NeutIndex "i8" -> return ()
      _ :< NeutIndex "i16" -> return ()
      _ :< NeutIndex "i32" -> return ()
      _ :< NeutIndex "i64" -> return ()
      _ :< NeutIndex "u8" -> return ()
      _ :< NeutIndex "u16" -> return ()
      _ :< NeutIndex "u32" -> return ()
      _ :< NeutIndex "u64" -> return ()
      _ :< NeutIndex "f8" -> return ()
      _ :< NeutIndex "f16" -> return ()
      _ :< NeutIndex "f32" -> return ()
      _ :< NeutIndex "f64" -> return ()
      t ->
        lift $
        throwE $
        "the type of " ++
        x ++ " is supposed to be a number, but is " ++ Pr.ppShow t
