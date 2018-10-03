module Infer
  ( check
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
  liftIO $ putStrLn $ "nonLinear: " ++ Pr.ppShow (nonLinear e)
  env <- get
  sub <- solve $ constraintEnv env
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
  higherUniv <- boxUniv
  -- obtain the type of e1
  tPi <- infer ctx e1 -- forall (x : tdom). tcod
  tPi' <- reduce tPi
  -- infer the type of e2, and obtain (tdom, udom)
  tdom <- infer ctx e2
  udom <- infer ctx tdom >>= annot higherUniv
  case tPi' of
    _ :< NeutPi (x, tdom') tcod' -> do
      insConstraintEnv ctx tdom tdom' udom
      returnMeta meta $ subst [(x, e2)] tcod'
    _ -> do
      x <- newNameOfType tdom
      -- represent (tcod, ucod) using hole
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
      indexMeta <- newNameWith "meta"
      u <- boxUniv
      insTypeEnv indexMeta u
      returnMeta meta $ indexMeta :< NeutIndex k
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
  insConstraintEnv ctx udom ub higherUniv
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

simp :: Constraint -> WithEnv Constraint
simp [] = return []
simp ((_, _ :< NeutVar s1, _ :< NeutVar s2, _):cs)
  | s1 == s2 = simp cs
simp ((ctx, _ :< NeutPi (x, tdom1) tcod1, _ :< NeutPi (y, tdom2) tcod2, univ):cs) = do
  var <- toVar x
  cs' <- sConstraint [(y, var)] cs >>= simp
  return $
    (ctx, tdom1, tdom2, univ) :
    (ctx ++ [x], tcod1, subst [(y, var)] tcod2, univ) : cs'
simp ((ctx, _ :< NeutPiIntro (x, _) body1, _ :< NeutPiIntro (y, _) body2, _ :< NeutPi (z, _) tcod):cs) = do
  var <- toVar z
  simp $ (ctx ++ [z], subst [(x, var)] body1, subst [(y, var)] body2, tcod) : cs
simp ((ctx, _ :< NeutPiIntro (x, _) body1, e2, _ :< NeutPi (z, _) tcod):cs) = do
  var <- toVar x
  let tcod' = subst [(z, var)] tcod
  appMeta <- newNameOfType tcod'
  let app = appMeta :< NeutPiElim e2 var
  simp $ (ctx ++ [x], body1, app, tcod') : cs
simp ((ctx, e1, e2@(_ :< NeutPiIntro _ _), t@(_ :< NeutPi _ _)):cs) =
  simp $ (ctx, e2, e1, t) : cs
simp ((ctx, _ :< NeutSigma [(x, tdom1)] tcod1, _ :< NeutSigma [(y, tdom2)] tcod2, univ):cs) = do
  var <- toVar x
  cs' <- sConstraint [(y, var)] cs >>= simp
  return $
    (ctx, tdom1, tdom2, univ) :
    (ctx ++ [x], tcod1, subst [(y, var)] tcod2, univ) : cs'
simp ((ctx, i :< NeutSigma ((x, tdom1):xts) tcod1, j :< NeutSigma ((y, tdom2):yts) tcod2, univ):cs) = do
  let sig1 = i :< NeutSigma [(x, tdom1)] (i :< NeutSigma xts tcod1)
  let sig2 = j :< NeutSigma [(y, tdom2)] (j :< NeutSigma yts tcod2)
  simp ((ctx, sig1, sig2, univ) : cs)
simp ((ctx, _ :< NeutSigmaIntro es1, _ :< NeutSigmaIntro es2, _ :< NeutSigma xts t):cs)
  | length es1 == length es2 = do
    let ts = map snd xts ++ [t]
    let sub = zip (map fst xts) es1
    let ts' = map (subst sub) ts
    newCs <-
      forM (zip (zip es1 es2) ts') $ \((e1, e2), t') -> return (ctx, e1, e2, t')
    simp $ newCs ++ cs
simp ((ctx, _ :< NeutSigmaIntro es, e2, _ :< NeutSigma xts t):cs)
  | length xts + 1 == length es = do
    prList <- projectionList e2 (xts, t)
    let sub = zip (map fst xts) es
    let ts = map (subst sub) $ map snd xts ++ [t]
    newCs <-
      forM (zip3 es prList ts) $ \(e, ithProj, t) -> return (ctx, e, ithProj, t)
    simp $ newCs ++ cs
simp ((ctx, e1, e2@(_ :< NeutSigmaIntro es), t@(_ :< NeutSigma xts _)):cs)
  | length xts + 1 == length es = simp $ (ctx, e2, e1, t) : cs
simp ((ctx, _ :< NeutBox t1, _ :< NeutBox t2, univ):cs) =
  simp $ (ctx, t1, t2, univ) : cs
simp ((ctx, _ :< NeutBoxIntro e1, _ :< NeutBoxIntro e2, _ :< NeutBox t):cs) =
  simp $ (ctx, e1, e2, t) : cs
simp ((_, _ :< NeutIndex l1, _ :< NeutIndex l2, _):cs)
  | l1 == l2 = simp cs
simp ((_, _ :< NeutUniv i, _ :< NeutUniv j, _):cs) = do
  insUnivConstraintEnv i j
  simp cs
simp (c:cs) = do
  cs' <- simp cs
  return $ c : cs'

solve :: Constraint -> WithEnv Subst
solve cs = do
  cs' <- simp cs
  (s1, cs1) <- solvePat cs'
  case cs1 of
    [] -> return s1
    _ -> do
      mcs2 <- solveDelta cs1
      case mcs2 of
        Just cs2 -> do
          s2 <- solve cs2
          return $ compose s1 s2
        Nothing -> lift $ throwE $ "couldn't solve: " ++ Pr.ppShow cs1

solvePat :: Constraint -> WithEnv (Subst, Constraint)
solvePat [] = return ([], [])
solvePat (c@(_, e1, e2, _):cs)
  | Just (x, args) <- headMeta [] e1 = do
    let (fvs, fmvs) = varAndHole e2
    if affineCheck args fvs && x `notElem` fmvs
      then do
        ans <- bindFormalArgs args e2
        cs' <- sConstraint [(x, ans)] cs
        (sub, cs'') <- solvePat cs'
        let sub' = compose sub [(x, ans)]
        return (sub', cs'')
      else do
        liftIO $ putStrLn "affineCheck failed"
        return ([], c : cs)
solvePat ((ctx, e1, e2, t):cs)
  | Just _ <- headMeta [] e2 = solvePat $ (ctx, e2, e1, t) : cs
solvePat (c:cs) = do
  (sub, cs') <- solvePat cs
  return (sub, c : cs')

-- solvePat cs = return ([], cs)
solveDelta :: Constraint -> WithEnv (Maybe Constraint)
solveDelta [] = return Nothing
solveDelta ((_, _ :< NeutVar s, t2, _):cs) = do
  liftIO $ putStrLn $ "found a var-substition:\n" ++ Pr.ppShow (s, t2)
  cs' <- sConstraint [(s, t2)] $ removeIdentFromCtx s cs
  return (Just cs')
solveDelta ((_, t1, _ :< NeutVar s, _):cs) = do
  liftIO $ putStrLn $ "found a var-substition:\n" ++ Pr.ppShow (s, t1)
  cs' <- sConstraint [(s, t1)] $ removeIdentFromCtx s cs
  return $ Just cs'
solveDelta (c:cs) = do
  mcs' <- solveDelta cs
  case mcs' of
    Nothing  -> return Nothing
    Just cs' -> return $ Just $ c : cs'

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

sConstraint :: Subst -> Constraint -> WithEnv Constraint
sConstraint s ctcs = do
  let (ctxList, cs, typeList) = split ctcs
  let (ts1, ts2) = unzip cs
  let ts1' = map (subst s) ts1
  let ts2' = map (subst s) ts2
  let typeList' = map (subst s) typeList
  return $ unsplit ctxList (zip ts1' ts2') typeList'

removeIdentFromCtx :: Identifier -> Constraint -> Constraint
removeIdentFromCtx _ [] = []
removeIdentFromCtx x ((ctx, e1, e2, t):cs) = do
  let ctx' = filter (/= x) ctx
  let cs' = removeIdentFromCtx x cs
  (ctx', e1, e2, t) : cs'

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
