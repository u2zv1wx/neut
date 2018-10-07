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

import qualified Data.PQueue.Min            as Q

check :: Identifier -> Neut -> WithEnv Neut
check main e = do
  t <- infer [] e
  insTypeEnv main t -- insert the type of main function
  boxConstraint [] $ nonLinear e
  liftIO $ putStrLn $ "nonLinear: " ++ Pr.ppShow (nonLinear e)
  gets constraintEnv >>= analyze
  gets constraintQueue >>= synthesize
  sub <- gets substitution
  env <- get
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
infer ctx (meta :< NeutPi (s, tdom) tcod) = do
  insTypeEnv s tdom
  higherUniv <- boxUniv
  udom <- infer ctx tdom >>= annot higherUniv
  ucod <- infer (ctx ++ [s]) tcod >>= annot higherUniv
  ub <- boxUniv >>= annot higherUniv
  insConstraintEnv ctx udom ub higherUniv
  insConstraintEnv (ctx ++ [s]) udom ucod higherUniv
  returnMeta meta higherUniv
infer ctx (meta :< NeutPiIntro (s, tdom) e) = do
  univ <- boxUniv
  tdom' <- annot univ tdom
  insTypeEnv s tdom'
  let ctx' = ctx ++ [s]
  tcod <- infer ctx' e >>= annot univ
  typeMeta <- newName' "meta" univ
  returnMeta meta $ typeMeta :< NeutPi (s, tdom') tcod
infer ctx (meta :< NeutPiElim e1 e2) = do
  univ <- boxUniv
  -- obtain the type of e1
  tPi <- infer ctx e1 >>= reduce -- forall (x : tdom). tcod
  -- infer the type of e2, and obtain (tdom, udom)
  tdom <- infer ctx e2 >>= annot univ
  case tPi of
    _ :< NeutPi (x, tdom') tcod' -> do
      insConstraintEnv ctx tdom tdom' univ
      returnMeta meta $ subst [(x, e2)] tcod'
    _ -> do
      x <- newNameOfType tdom
      -- represent tcod using hole
      tcod <- appCtx (ctx ++ [x]) >>= annot univ
      -- add a constraint regarding the Pi-type
      typeMeta <- newNameWith "meta"
      insTypeEnv typeMeta univ
      insConstraintEnv ctx tPi (typeMeta :< NeutPi (x, tdom) tcod) univ
      -- return the type of this elimination
      returnMeta meta $ subst [(x, e2)] tcod
infer ctx (_ :< NeutSigma xts t) = do
  forM_ xts $ uncurry insTypeEnv
  higherUniv <- boxUniv
  univ <- boxUniv >>= annot higherUniv
  forM_ (map snd xts ++ [t]) $ \t -> do
    u <- infer ctx t
    insConstraintEnv ctx u univ higherUniv
  return univ
infer _ (_ :< NeutSigmaIntro []) = undefined
infer _ (_ :< NeutSigmaIntro [_]) = undefined
infer ctx (meta :< NeutSigmaIntro es) = do
  univ <- boxUniv
  ts <- mapM (infer ctx) es
  forM_ ts $ annot univ
  xs <- forM ts newNameOfType
  holeList <- sigmaHole ctx xs
  let holeList' = map (subst (zip xs es)) holeList
  forM_ (zip holeList' ts) $ \(h, t) -> insConstraintEnv ctx h t univ
  let binder = zip xs (take (length holeList - 1) holeList)
  wrapTypeWithUniv univ (NeutSigma binder (last holeList)) >>= returnMeta meta
infer ctx (meta :< NeutSigmaElim e1 xs e2) = do
  univ <- boxUniv
  t1 <- infer ctx e1 >>= annot univ
  holeList <- sigmaHole ctx xs
  forM_ (zip xs holeList) $ uncurry insTypeEnv
  t2 <- infer ctx e2 >>= annot univ
  let binder = zip xs (take (length holeList - 1) holeList)
  let cod = last holeList
  sigmaType <- wrapType $ NeutSigma binder cod
  insConstraintEnv ctx t1 sigmaType univ
  z <- newNameOfType t1
  pair <- constructPair (ctx ++ xs) xs
  typeC <- appCtx (ctx ++ xs ++ [z])
  insConstraintEnv ctx t2 (subst [(z, pair)] typeC) univ
  returnMeta meta $ subst [(z, e1)] typeC
infer ctx (meta :< NeutBox t) = infer ctx t >>= returnMeta meta
infer ctx (meta :< NeutBoxIntro e) = do
  univ <- boxUniv
  t <- infer ctx e >>= annot univ
  boxConstraint ctx $ var e
  wrapTypeWithUniv univ (NeutBox t) >>= returnMeta meta
infer ctx (meta :< NeutBoxElim e) = do
  univ <- boxUniv
  t <- infer ctx e >>= annot univ
  resultHole <- appCtx ctx
  boxType <- wrapType $ NeutBox resultHole
  insConstraintEnv ctx t boxType univ
  boxConstraint ctx $ var e
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
  univ <- boxUniv
  trec <- appCtx ctx >>= annot univ
  insTypeEnv s trec
  te <- infer (ctx ++ [s]) e >>= annot univ
  insConstraintEnv ctx te trec univ
  returnMeta meta te
infer _ (meta :< NeutUniv _) = boxUniv >>= returnMeta meta
infer ctx (meta :< NeutHole _) = appCtx ctx >>= returnMeta meta

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

simp :: [PreConstraint] -> WithEnv [PreConstraint]
simp [] = return []
simp ((_, _ :< NeutVar s1, _ :< NeutVar s2, _):cs)
  | s1 == s2 = simp cs
simp ((ctx, _ :< NeutVar s1, e2, t):cs) = do
  me <- insDef s1 e2
  case me of
    Nothing -> simp cs
    Just e  -> simp $ (ctx, e, e2, t) : cs
simp ((ctx, e1, v@(_ :< NeutVar _), t):cs) = simp $ (ctx, v, e1, t) : cs
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
simp (c@(_, e1, _, _):cs)
  | Just _ <- headMeta' [] e1 = do
    cs' <- simp cs
    return $ c : cs'
simp (c@(_, _, e2, _):cs)
  | Just _ <- headMeta' [] e2 = do
    cs' <- simp cs
    return $ c : cs'
simp (c:_) = lift $ throwE $ "cannot simplify:\n" ++ Pr.ppShow c

categorize :: PreConstraint -> Constraint
categorize (ctx, _ :< NeutVar x, e2, t) = do
  let c = ConstraintBeta x e2
  Constraint ctx c t
categorize (ctx, e1, e2@(_ :< NeutVar _), t) = categorize (ctx, e2, e1, t)
categorize (ctx, e1, e2, t)
  | (_ :< NeutVar x, metaArgs1) <- toPiElimSeq e1
  , (_ :< NeutVar y, metaArgs2) <- toPiElimSeq e2
  , x == y
  , length metaArgs1 == length metaArgs2 = do
    let c = ConstraintDelta x (map snd metaArgs1) (map snd metaArgs2)
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta [] e1
  , let (fvs, fmvs) = varAndHole e2
  , affineCheck args fvs && x `notElem` fmvs = do
    let c = ConstraintPattern x args e2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta [] e1
  , let (fvs, fmvs) = varAndHole e2
  , affineCheck args fvs && x `notElem` fmvs = categorize (ctx, e2, e1, t)
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta [] e1 = do
    let c = ConstraintQuasiPattern x args e2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just _ <- headMeta [] e2 = categorize (ctx, e2, e1, t)
categorize (ctx, e1, e2, t)
  | Just (x, args1) <- headMeta' [] e1
  , Just (y, args2) <- headMeta' [] e2 = do
    let c = ConstraintFlexFlex x args1 y args2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just (x, args) <- headMeta' [] e1 = do
    let c = ConstraintFlexRigid x args e2
    Constraint ctx c t
categorize (ctx, e1, e2, t)
  | Just _ <- headMeta' [] e2 = categorize (ctx, e2, e1, t)
categorize c = error $ "categorize: invalid argument:\n" ++ Pr.ppShow c

analyze :: [PreConstraint] -> WithEnv ()
analyze cs = simp cs >>= mapM_ analyze'

analyze' :: PreConstraint -> WithEnv ()
analyze' c@(ctx, e1, e2, t) = do
  sub <- gets substitution
  case categorize c of
    Constraint _ (ConstraintPattern hole _ _) _
      | Just e <- lookup hole sub -> do
        cs <- simp [(ctx, subst [(hole, e)] e1, subst [(hole, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintQuasiPattern hole _ _) _
      | Just e <- lookup hole sub -> do
        cs <- simp [(ctx, subst [(hole, e)] e1, subst [(hole, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintFlexRigid hole _ _) _
      | Just e <- lookup hole sub -> do
        cs <- simp [(ctx, subst [(hole, e)] e1, subst [(hole, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintFlexFlex hole1 _ _ _) _
      | Just e <- lookup hole1 sub -> do
        cs <- simp [(ctx, subst [(hole1, e)] e1, subst [(hole1, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintFlexFlex _ _ hole2 _) _
      | Just e <- lookup hole2 sub -> do
        cs <- simp [(ctx, subst [(hole2, e)] e1, subst [(hole2, e)] e2, t)]
        analyze cs
    Constraint _ (ConstraintPattern hole args e) _ -> do
      ans <- bindFormalArgs args e
      modify (\e -> e {substitution = (hole, ans) : substitution e})
      mmap <- gets metaMap
      analyze $ map snd $ filter (\(y, _) -> y == hole) mmap
    _ -> do
      let c' = categorize c
      modify (\e -> e {constraintQueue = Q.insert c' $ constraintQueue e})
      case c' of
        (Constraint _ (ConstraintQuasiPattern hole _ _) _) ->
          modify (\e -> e {metaMap = (hole, c) : metaMap e})
        (Constraint _ (ConstraintFlexRigid hole _ _) _) ->
          modify (\e -> e {metaMap = (hole, c) : metaMap e})
        (Constraint _ (ConstraintFlexFlex hole1 _ hole2 _) _) -> do
          modify (\e -> e {metaMap = (hole1, c) : metaMap e})
          modify (\e -> e {metaMap = (hole2, c) : metaMap e})
        _ -> return ()

resolve :: Justification -> WithEnv ()
resolve j = do
  stack <- gets caseStack
  resolve' j stack

resolve' :: Justification -> [Case] -> WithEnv ()
resolve' _ [] = lift $ throwE "failed to resolvelve the case-split"
resolve' j (c:cs)
  | j `depends` caseJustification c = do
    restoreState c
    case alternatives c of
      []    -> resolve' j cs
      (a:_) -> analyze a
resolve' j (_:cs) = resolve' j cs

restoreState :: Case -> WithEnv ()
restoreState c =
  modify
    (\e ->
       e
         { constraintQueue = constraintQueueSnapshot c
         , metaMap = metaMapSnapshot c
         , substitution = substitutionSnapshot c
         })

process :: [[PreConstraint]] -> Justification -> WithEnv ()
process [] j = resolve j
process z@(a:_) j = do
  ja <- Assumption <$> newNameWith "j"
  c <- newCaseSplit ja z
  modify (\e -> e {caseStack = c : caseStack e})
  analyze a

newCaseSplit :: Justification -> [[PreConstraint]] -> WithEnv Case
newCaseSplit ja z = do
  q <- gets constraintQueue
  mmap <- gets metaMap
  sub <- gets substitution
  return $
    Case
      { constraintQueueSnapshot = q
      , metaMapSnapshot = mmap
      , substitutionSnapshot = sub
      , caseJustification = ja
      , savedJustification = ja
      , alternatives = z
      }

synthesize :: Q.MinQueue Constraint -> WithEnv ()
synthesize q = do
  liftIO $ putStrLn $ Pr.ppShow q
  case Q.getMin q of
    Nothing -> return ()
    Just c -> do
      q' <- synthesize' c
      synthesize $ Q.deleteMin q `Q.union` q'

synthesize' :: Constraint -> WithEnv (Q.MinQueue Constraint)
synthesize' (Constraint _ (ConstraintPattern x args e) _) = do
  ans <- bindFormalArgs args e
  modify (\e -> e {substitution = (x, ans) : substitution e})
  mmap <- gets metaMap
  getQueue $ analyze $ map snd $ filter (\(y, _) -> y == x) mmap
synthesize' (Constraint ctx (ConstraintBeta x body) t) = do
  me <- insDef x body
  case me of
    Nothing -> return Q.empty
    Just body' -> Q.fromList . map categorize <$> simp [(ctx, body, body', t)]
synthesize' (Constraint ctx (ConstraintDelta x args1 args2) t) = do
  sub <- gets substitution
  liftIO $ putStrLn $ Pr.ppShow sub
  a1 <- simp $ map (\(e1, e2) -> (ctx, e1, e2, t)) $ zip args1 args2
  j <- Assumption <$> newNameWith "j"
  case lookup x sub of
    Nothing -> getQueue $ process [a1] j
    Just e -> do
      e1' <- appFold' e args1 >>= reduce
      e2' <- appFold' e args2 >>= reduce
      a2 <- simp [(ctx, e1', e2', t)]
      getQueue $ process [a1, a2] j
synthesize' (Constraint ctx (ConstraintQuasiPattern hole preArgs e) t) = do
  args <- mapM toVar preArgs
  synthesize' (Constraint ctx (ConstraintFlexRigid hole args e) t)
synthesize' (Constraint ctx (ConstraintFlexRigid hole args e) t)
  | (x@(_ :< NeutVar _), eArgs) <- toPiElimSeq e = do
    let candList = x : args
    newHoleList <- mapM (const (newNameWith "hole") >=> toVar) args
    newArgList <- mapM (const $ newNameWith "arg") eArgs
    newVarList <- mapM toVar newArgList
    argList <- forM newHoleList $ \h -> appFold' h newVarList
    bodyList <- forM candList $ \v -> appFold' v argList
    lamList <- forM bodyList $ \body -> bindFormalArgs newArgList body
    as <-
      forM lamList $ \lam -> do
        left <- appFold' lam args
        meta <- newNameWith "meta"
        simp [(ctx, left, e, t), (ctx, meta :< NeutHole hole, lam, t)]
    j <- Assumption <$> newNameWith "j"
    getQueue $ process as j
synthesize' (Constraint _ c _) =
  lift $ throwE $ "cannot synthesize:\n" ++ Pr.ppShow c

getQueue :: WithEnv a -> WithEnv (Q.MinQueue Constraint)
getQueue command = do
  modify (\e -> e {constraintQueue = Q.empty})
  command
  gets constraintQueue

insDef :: Identifier -> Neut -> WithEnv (Maybe Neut)
insDef x body = do
  sub <- gets substitution
  modify (\e -> e {substitution = (x, body) : substitution e})
  return $ lookup x sub

headMeta :: [Identifier] -> Neut -> Maybe (Identifier, [Identifier])
headMeta args (_ :< NeutPiElim e1 (_ :< NeutVar x)) = headMeta (x : args) e1
headMeta args (_ :< NeutHole x)                     = Just (x, args)
headMeta _ _                                        = Nothing

headMeta' :: [Neut] -> Neut -> Maybe (Identifier, [Neut])
headMeta' args (_ :< NeutPiElim e1 e2) = headMeta' (e2 : args) e1
headMeta' args (_ :< NeutHole x)       = Just (x, args)
headMeta' _ _                          = Nothing

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

sConstraint :: Subst -> [PreConstraint] -> WithEnv [PreConstraint]
sConstraint s ctcs = do
  let (ctxList, cs, typeList) = split ctcs
  let (ts1, ts2) = unzip cs
  let ts1' = map (subst s) ts1
  let ts2' = map (subst s) ts2
  let typeList' = map (subst s) typeList
  return $ unsplit ctxList (zip ts1' ts2') typeList'

split :: [PreConstraint] -> ([[Identifier]], [(Neut, Neut)], [Neut])
split [] = ([], [], [])
split ((ctx, e1, e2, t):rest) = do
  let (ctxList, cs, typeList) = split rest
  (ctx : ctxList, (e1, e2) : cs, t : typeList)

unsplit :: [[Identifier]] -> [(Neut, Neut)] -> [Neut] -> [PreConstraint]
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
