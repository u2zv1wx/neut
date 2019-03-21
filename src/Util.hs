module Util where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Trans.Except

import Control.Comonad
import Control.Comonad.Cofree

import Control.Monad.State

import Data
import Reduce

import Data.Maybe (fromMaybe)

import qualified Text.Show.Pretty as Pr

import qualified Data.Map.Strict as Map

import Debug.Trace

import System.Directory
import System.FilePath
  -- fromPiIntroSeq (meta :< NeutPiIntro (x, t) e, rest)

toNegPiIntroSeq :: Neg -> (Neg, [Identifier])
toNegPiIntroSeq (NegPiIntro x body) = do
  let (body', args) = toNegPiIntroSeq body
  (body', x : args)
toNegPiIntroSeq t = (t, [])

toNegPiElimSeq :: Neg -> (Neg, [Pos])
toNegPiElimSeq (NegPiElim e1 e2) = do
  let (fun, xs) = toNegPiElimSeq e1
  (fun, e2 : xs)
toNegPiElimSeq c = (c, [])

toPiSeq :: Neut -> (Neut, [(Identifier, Neut)])
toPiSeq (_ :< NeutPi (x, t) body) = do
  let (body', args) = toPiSeq body
  (body', (x, t) : args)
toPiSeq t = (t, [])

-- toSigmaSeq :: Neut -> (Neut, [(Identifier, Neut)])
-- toSigmaSeq (_ :< NeutSigma (x, t) body) = do
--   let (body', args) = toSigmaSeq body
--   (body', (x, t) : args)
-- toSigmaSeq t = (t, [])
-- toSigmaSeqTerm :: Term -> (Term, [(Identifier, Term)])
-- toSigmaSeqTerm (TermSigma (x, t) body) = do
--   let (body', args) = toSigmaSeqTerm body
--   (body', (x, t) : args)
-- toSigmaSeqTerm t = (t, [])
var :: Neut -> [Identifier]
var e = fst $ varAndHole e

varAndHole :: Neut -> ([Identifier], [Identifier])
varAndHole (_ :< NeutVar s) = ([s], [])
varAndHole (_ :< NeutPi (x, tdom) tcod) = do
  let vs1 = varAndHole tdom
  let (vs21, vs22) = varAndHole tcod
  let vs2 = (filter (/= x) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< NeutPiIntro (x, _) e) = do
  let (vs1, vs2) = varAndHole e
  (filter (/= x) vs1, vs2)
varAndHole (_ :< NeutPiElim e1 e2) =
  pairwiseConcat [varAndHole e1, varAndHole e2]
varAndHole (_ :< NeutSigma xts) = varAndHoleSigma xts
varAndHole (_ :< NeutSigmaIntro es) = pairwiseConcat $ map varAndHole es
varAndHole (_ :< NeutSigmaElim e1 xs e2) = do
  let vs1 = varAndHole e1
  let (vs21, vs22) = varAndHole e2
  let vs2 = (filter (`notElem` xs) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< NeutIndex _) = ([], [])
varAndHole (_ :< NeutIndexIntro _) = ([], [])
varAndHole (_ :< NeutIndexElim e branchList) = do
  let vs1 = varAndHole e
  let select i = filter (`notElem` varIndex i)
  vss <-
    forM branchList $ \(i, body) -> do
      let (vs21, vs22) = varAndHole body
      return (select i vs21, vs22)
  pairwiseConcat (vs1 : vss)
varAndHole (_ :< NeutConst _) = ([], [])
varAndHole (_ :< NeutUniv _) = ([], [])
varAndHole (_ :< NeutMu _ e) = varAndHole e
varAndHole (_ :< NeutHole x) = ([], [x])

varAndHoleSigma :: [(Identifier, Neut)] -> ([Identifier], [Identifier])
varAndHoleSigma [] = ([], [])
varAndHoleSigma ((x, t):xts) = do
  let vs1 = varAndHole t
  let (vs21, vs22) = varAndHoleSigma xts
  let vs2 = (filter (/= x) vs21, vs22)
  pairwiseConcat [vs1, vs2]

varPos :: Pos -> [Identifier]
varPos (PosVar s) = [s]
varPos (PosConst _) = []
varPos (PosSigma xts) = do
  let (xs, ts) = unzip xts
  let vs = concatMap varPos ts
  filter (`notElem` xs) vs
varPos (PosSigmaIntro es) = concatMap varPos es
varPos (PosIndex _) = []
varPos (PosIndexIntro _ _) = []
varPos (PosDown e) = varNeg e
varPos (PosDownIntro e) = varNeg e
varPos PosUniv = []

varNeg :: Neg -> [Identifier]
varNeg (NegPi (x, tdom) tcod) = do
  let vs1 = varPos tdom
  let vs2 = filter (/= x) $ varNeg tcod
  vs1 ++ vs2
varNeg (NegPiIntro x e) = do
  let vs = varNeg e
  filter (/= x) vs
varNeg (NegPiElim e1 e2) = varNeg e1 ++ varPos e2
varNeg (NegSigmaElim e1 xs e2) = do
  let vs1 = varPos e1
  let vs2 = filter (`notElem` xs) $ varNeg e2
  vs1 ++ vs2
varNeg (NegIndexElim e branchList) = do
  let vs1 = varPos e
  let select (i, body) = filter (`notElem` varIndex i) (varNeg body)
  let vs2 = concatMap select branchList
  vs1 ++ vs2
varNeg (NegUpIntro e) = varPos e
varNeg (NegUpElim x e1 e2) = do
  let vs1 = varNeg e1
  let vs2 = filter (/= x) $ varNeg e2
  vs1 ++ vs2
varNeg (NegDownElim e) = varPos e
varNeg (NegMu x e) = filter (/= x) $ varNeg e

isLinear :: Identifier -> [Identifier] -> [Identifier]
isLinear x xs =
  if length (filter (== x) xs) == 1
    then []
    else [x]

isAffine :: Identifier -> [Identifier] -> [Identifier]
isAffine x xs =
  if length (filter (== x) xs) <= 1
    then []
    else [x]

foldML ::
     (Cofree f Identifier -> a -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldML _ e [] = return e
foldML f e (t:ts) = do
  let tmp = f e t
  i <- newName
  foldML f (i :< tmp) ts

foldMR ::
     (a -> Cofree f Identifier -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldMR _ e [] = return e
foldMR f e (t:ts) = do
  tmp <- foldMR f e ts
  let x = f t tmp
  i <- newName
  return $ i :< x

appFold :: Neut -> [Neut] -> WithEnv Neut
appFold e [] = return e
appFold e@(i :< _) (term:ts) = do
  t <- lookupTypeEnv' i
  case t of
    _ :< NeutPi _ tcod -> do
      meta <- newNameWith "meta"
      insTypeEnv meta tcod
      appFold (meta :< NeutPiElim e term) ts
    _ -> do
      e' <- nonRecReduce e
      lift $ throwE $ "appfold. t:\n" ++ Pr.ppShow t ++ "\ne:\n" ++ Pr.ppShow e'
      -- error "Lift.appFold"

appFold' :: Neut -> [Neut] -> WithEnv Neut
appFold' e [] = return e
appFold' e (term:ts) = do
  meta <- newNameWith "meta"
  appFold' (meta :< NeutPiElim e term) ts

constructFormalArgs :: [Identifier] -> WithEnv [Identifier]
constructFormalArgs [] = return []
constructFormalArgs (ident:is) = do
  varType <- lookupTypeEnv' ident
  formalArg <- newNameWith "arg"
  insTypeEnv formalArg varType
  args <- constructFormalArgs is
  return $ formalArg : args

bindFormalArgs :: [Identifier] -> Neut -> WithEnv Neut
bindFormalArgs [] terminal = return terminal
bindFormalArgs (arg:xs) c@(metaLam :< _) = do
  tLam@(tLamMeta :< _) <- lookupTypeEnv'' metaLam
  tArg@(tArgMeta :< _) <- lookupTypeEnv' arg
  tmp <- bindFormalArgs xs c
  meta <- newNameWith "meta"
  univMeta <- newNameWith "meta"
  univ <- boxUniv
  insTypeEnv tArgMeta univ
  insTypeEnv tLamMeta univ
  insTypeEnv univMeta univ
  insTypeEnv meta (univMeta :< NeutPi (arg, tArg) tLam)
  return $ meta :< NeutPiIntro (arg, tArg) tmp

bindFormalArgs' :: [Identifier] -> Neut -> WithEnv Neut
bindFormalArgs' [] terminal = return terminal
bindFormalArgs' (arg:xs) c = do
  tmp <- bindFormalArgs' xs c
  meta <- newNameWith "meta"
  h <- newNameWith "hole"
  holeMeta <- newNameWith "meta"
  return $ meta :< NeutPiIntro (arg, holeMeta :< NeutHole h) tmp

abstractPi :: [Identifier] -> Neut -> WithEnv Neut
abstractPi [] terminal = return terminal
abstractPi (x:xs) c = do
  tmp <- abstractPi xs c
  meta <- newNameWith "meta"
  t <- lookupTypeEnv' x
  return $ meta :< NeutPi (x, t) tmp

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

boxUniv :: WithEnv Neut
boxUniv = do
  univMeta <- newNameWith "meta"
  -- boxMeta <- newNameWith "meta"
  l <- newName
  return $ univMeta :< NeutUniv (UnivLevelHole l)

lookupTypeEnv'' :: String -> WithEnv Neut
lookupTypeEnv'' s = do
  mt <- gets (Map.lookup s . typeEnv)
  case mt of
    Just t -> return t
    Nothing -> boxUniv

toVar :: Identifier -> WithEnv Neut
toVar x = do
  t <- lookupTypeEnv' x
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutVar x

toVar1 :: Identifier -> Neut -> WithEnv Neut
toVar1 x t = do
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutVar x

toVar' :: Identifier -> WithEnv Neut
toVar' x = do
  meta <- newNameWith "meta"
  return $ meta :< NeutVar x

substCode :: [(String, Data)] -> Code -> Code
substCode sub (CodeReturn ans) = CodeReturn $ substData sub ans
substCode sub (CodeLet x d cont) =
  CodeLet x (substData sub d) $ substCode sub cont
substCode sub (CodeCall x name xds cont) = do
  let name' = substData sub name
  let xds' = map (substData sub) xds
  CodeCall x name' xds' $ substCode sub cont
substCode sub (CodeCallTail name xds) = do
  let name' = substData sub name
  let xds' = map (substData sub) xds
  CodeCallTail name' xds'
substCode sub (CodeSwitch y branchList) = do
  let y' = substData sub y
  let (labelList, es) = unzip branchList
  let es' = map (substCode sub) es
  CodeSwitch y' $ zip labelList es'
substCode sub (CodeExtractValue x basePointer i cont) = do
  let basePointer' = substData sub basePointer
  CodeExtractValue x basePointer' i $ substCode sub cont
substCode sub (CodeFree x cont) = do
  let x' = substData sub x
  CodeFree x' $ substCode sub cont

substData :: [(String, Data)] -> Data -> Data
substData sub (DataLocal x) = fromMaybe (DataLocal x) (lookup x sub)
substData _ (DataGlobal x) = DataGlobal x
substData _ (DataInt i) = DataInt i
substData sub (DataStruct ds) = DataStruct $ map (substData sub) ds

expandDirPath :: FilePath -> IO FilePath
expandDirPath path = do
  current <- getCurrentDirectory
  -- note that, if `path` is an absolute path, `path` itself is returned here.
  return $ current </> path

isEq :: Neut -> Neut -> WithEnv Bool
isEq (_ :< NeutVar x1) (_ :< NeutVar x2) = return $ x1 == x2
isEq (_ :< NeutPi (x1, t11) t12) (_ :< NeutPi (x2, t21) t22) = do
  vx <- toVar' x1
  b1 <- isEq t11 t21
  b2 <- isEq t12 $ subst [(x2, vx)] t22
  return $ b1 && b2
isEq (_ :< NeutPiIntro (x1, t1) e1) (_ :< NeutPiIntro (x2, t2) e2) = do
  vx <- toVar' x1
  b1 <- isEq t1 t2
  b2 <- isEq e1 $ subst [(x2, vx)] e2
  return $ b1 && b2
isEq (_ :< NeutPiElim e11 e12) (_ :< NeutPiElim e21 e22) = do
  b1 <- isEq e11 e21
  b2 <- isEq e12 e22
  return $ b1 && b2
isEq (_ :< NeutSigma xts) (_ :< NeutSigma yts) = isEqSigma xts yts
  -- undefined
  -- vx <- toVar' x1
  -- b1 <- isEq t11 t21
  -- b2 <- isEq t12 $ subst [(x2, vx)] t22
  -- return $ b1 && b2
isEq (_ :< NeutSigmaIntro es1) (_ :< NeutSigmaIntro es2)
  | length es1 == length es2 = do
    bs <- zipWithM isEq es1 es2
    return $ and bs
isEq (_ :< NeutSigmaElim e11 xs1 e12) (_ :< NeutSigmaElim e21 xs2 e22)
  | length xs1 == length xs2 = do
    metaList <- mapM (const $ newNameWith "meta") xs1
    let vs = map (\(meta, x) -> meta :< NeutVar x) $ zip metaList xs1
    let sub = zip xs2 vs
    let e22' = subst sub e22
    b1 <- isEq e11 e21
    b2 <- isEq e12 e22'
    return $ b1 && b2
isEq (_ :< NeutIndex l1) (_ :< NeutIndex l2) = return $ l1 == l2
isEq (_ :< NeutIndexIntro i1) (_ :< NeutIndexIntro i2) = return $ i1 == i2
isEq (_ :< NeutIndexElim e1 bs1) (_ :< NeutIndexElim e2 bs2) = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch bs1 bs2
  return $ b1 && b2
isEq (_ :< NeutUniv l1) (_ :< NeutUniv l2) = return $ l1 == l2
isEq (_ :< NeutConst t1) (_ :< NeutConst t2) = return $ t1 == t2
isEq (_ :< NeutMu x1 e1) (_ :< NeutMu x2 e2) = do
  vx <- toVar' x1
  isEq e1 $ subst [(x2, vx)] e2
isEq (_ :< NeutHole x1) (_ :< NeutHole x2) = return $ x1 == x2
isEq _ _ = return False

isEqSigma :: [(Identifier, Neut)] -> [(Identifier, Neut)] -> WithEnv Bool
isEqSigma [] [] = return True
isEqSigma ((x, tx):xts) ((y, ty):yts) = do
  vx <- toVar' x
  b1 <- isEq tx ty
  let (ys, ts) = unzip yts
  let ts' = map (subst [(y, vx)]) ts
  let yts' = zip ys ts'
  b2 <- isEqSigma xts yts'
  return $ b1 && b2
isEqSigma _ _ = return False

isEqBranch :: [(IndexOrVar, Neut)] -> [(IndexOrVar, Neut)] -> WithEnv Bool
isEqBranch [] [] = return True
isEqBranch ((Right x1, e1):es1) ((Right x2, e2):es2) = do
  vx <- toVar' x1
  b1 <- isEq e1 $ subst [(x2, vx)] e2
  b2 <- isEqBranch es1 es2
  return $ b1 && b2
isEqBranch ((Left (IndexLabel x1), e1):es1) ((Left (IndexLabel x2), e2):es2)
  | x1 == x2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((Left (IndexInteger i1), e1):es1) ((Left (IndexInteger i2), e2):es2)
  | i1 == i2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((Left (IndexFloat i1), e1):es1) ((Left (IndexFloat i2), e2):es2)
  | i1 == i2 = do
    b1 <- isEq e1 e2
    b2 <- isEqBranch es1 es2
    return $ b1 && b2
isEqBranch ((Left IndexDefault, e1):es1) ((Left IndexDefault, e2):es2) = do
  b1 <- isEq e1 e2
  b2 <- isEqBranch es1 es2
  return $ b1 && b2
isEqBranch _ _ = return False

headMeta :: [Identifier] -> Neut -> Maybe (Identifier, [Identifier])
headMeta args (_ :< NeutPiElim e1 (_ :< NeutVar x)) = headMeta (x : args) e1
headMeta args (_ :< NeutHole x) = Just (x, args)
headMeta _ _ = Nothing

headMeta' :: [Neut] -> Neut -> Maybe (Identifier, [Neut])
headMeta' args (_ :< NeutPiElim e1 e2) = headMeta' (e2 : args) e1
headMeta' args (_ :< NeutHole x) = Just (x, args)
headMeta' _ _ = Nothing

headMeta1 :: [Neut] -> Neut -> Maybe (Identifier, [Neut])
headMeta1 args (_ :< NeutPiElim e1 e2) = headMeta1 (e2 : args) e1
headMeta1 args (_ :< NeutVar x) = Just (x, args)
headMeta1 _ _ = Nothing

headMeta2 :: Neut -> Maybe Identifier
headMeta2 (_ :< NeutHole x) = Just x
headMeta2 (_ :< NeutPiElim e1 _) = headMeta2 e1
headMeta2 (_ :< NeutIndexElim e _) = headMeta2 e
headMeta2 _ = Nothing

headMeta'' :: Neut -> Maybe Identifier
headMeta'' (_ :< NeutVar x) = Just x
headMeta'' (_ :< NeutPiElim e1 _) = headMeta'' e1
headMeta'' (_ :< NeutIndexElim e _) = headMeta'' e
headMeta'' _ = Nothing

headMeta''' :: Neut -> Maybe (Identifier, Neut -> Neut)
headMeta''' (_ :< NeutVar x) = Just (x, id)
headMeta''' (i :< NeutPiElim e1 e2) = do
  (x, f) <- headMeta''' e1
  let g y = i :< NeutPiElim y e2
  return (x, g . f)
headMeta''' (i :< NeutIndexElim e branchList) = do
  (x, f) <- headMeta''' e
  return (x, (\y -> i :< NeutIndexElim y branchList) . f)
headMeta''' _ = Nothing

affineCheck :: [Identifier] -> [Identifier] -> Bool
affineCheck xs = affineCheck' xs xs

affineCheck' :: [Identifier] -> [Identifier] -> [Identifier] -> Bool
affineCheck' _ [] _ = True
affineCheck' xs (y:ys) fvs =
  if y `notElem` fvs
    then affineCheck' xs ys fvs
    else null (isLinear y xs) && affineCheck' xs ys fvs

sConstraint :: Subst -> [PreConstraint] -> WithEnv [PreConstraint]
sConstraint s ctcs = do
  let (ctxList, cs, typeList) = split ctcs
  let (ts1, ts2) = unzip cs
  let ts1' = map (subst s) ts1
  let ts2' = map (subst s) ts2
  let typeList' = map (subst s) typeList
  return $ unsplit ctxList (zip ts1' ts2') typeList'

insDef :: Identifier -> Neut -> WithEnv (Maybe Neut)
insDef x body = do
  body' <- nonRecReduce body
  sub <- gets substitution
  modify (\e -> e {substitution = (x, body') : substitution e})
  return $ lookup x sub

insDef' :: Identifier -> Neut -> WithEnv ()
insDef' x body = do
  body' <- nonRecReduce body
  modify (\e -> e {substitution = (x, body') : substitution e})

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

projectionList :: Neut -> [Neut] -> WithEnv [Neut]
projectionList e ts = do
  xiList <- forM ts $ \t -> newNameOfType t
  metaList <- mapM (const newName) xiList
  let varList = map (\(m, x) -> m :< NeutVar x) $ zip metaList xiList
  forM varList $ \v -> do
    meta <- newName
    return $ meta :< NeutSigmaElim e xiList v

sizeOfLowType :: LowType -> Int
sizeOfLowType (LowTypeSignedInt i) = max i 64
sizeOfLowType (LowTypeUnsignedInt i) = max i 64
sizeOfLowType (LowTypeFloat i) = max i 64
sizeOfLowType _ = 64

sizeOf :: Neut -> Int
sizeOf (_ :< NeutIndex "i1") = 1
sizeOf (_ :< NeutIndex "i2") = 2
sizeOf (_ :< NeutIndex "i4") = 4
sizeOf (_ :< NeutIndex "i8") = 8
sizeOf (_ :< NeutIndex "i16") = 16
sizeOf (_ :< NeutIndex "i32") = 32
sizeOf (_ :< NeutIndex "i64") = 64
sizeOf (_ :< NeutIndex "u1") = 1
sizeOf (_ :< NeutIndex "u2") = 2
sizeOf (_ :< NeutIndex "u4") = 4
sizeOf (_ :< NeutIndex "u8") = 8
sizeOf (_ :< NeutIndex "u16") = 16
sizeOf (_ :< NeutIndex "u32") = 32
sizeOf (_ :< NeutIndex "u64") = 64
sizeOf (_ :< NeutIndex "f16") = 16
sizeOf (_ :< NeutIndex "f32") = 32
sizeOf (_ :< NeutIndex "f64") = 64
sizeOf _ = 64

hasMeta :: Neut -> Bool
hasMeta (_ :< NeutVar _) = False
hasMeta (_ :< NeutPi (_, tdom) tcod) = hasMeta tdom || hasMeta tcod
hasMeta (_ :< NeutPiIntro _ e) = hasMeta e
hasMeta (_ :< NeutPiElim e1 e2) = hasMeta e1 || hasMeta e2
hasMeta (_ :< NeutSigma xts) = do
  let (_, ts) = unzip xts
  any hasMeta ts
hasMeta (_ :< NeutSigmaIntro es) = any hasMeta es
hasMeta (_ :< NeutSigmaElim e1 _ e2) = hasMeta e1 || hasMeta e2
hasMeta (_ :< NeutIndex _) = False
hasMeta (_ :< NeutIndexIntro _) = False
hasMeta (_ :< NeutIndexElim e branchList) = do
  let (_, es) = unzip branchList
  any hasMeta (e : es)
hasMeta (_ :< NeutUniv _) = False
hasMeta (_ :< NeutConst _) = False
hasMeta (_ :< NeutMu _ e) = hasMeta e
hasMeta (_ :< NeutHole _) = True

depth :: Identifier -> WithEnv Int
depth x = do
  sub <- gets substitution
  case lookup x sub of
    Nothing -> return 0
    Just e -> do
      let vs = var e
      ds <- mapM depth vs
      return $ 1 + maximum ds

toTermForDebug :: Neut -> WithEnv Term
toTermForDebug (_ :< NeutVar s) = return $ TermVar s
toTermForDebug (_ :< NeutPi (s, tdom) tcod) = do
  tdom' <- toTermForDebug tdom
  tcod' <- toTermForDebug tcod
  return $ TermPi (s, tdom') tcod'
toTermForDebug (_ :< NeutPiIntro (s, _) e) = do
  e' <- toTermForDebug e
  return $ TermPiIntro s e'
toTermForDebug (_ :< NeutPiElim e v) = do
  e' <- toTermForDebug e
  v' <- toTermForDebug v
  return $ TermPiElim e' v'
toTermForDebug (_ :< NeutSigma xts) = do
  undefined
toTermForDebug (_ :< NeutSigmaIntro es) = do
  es' <- mapM toTermForDebug es
  return $ TermSigmaIntro es'
toTermForDebug (_ :< NeutSigmaElim e1 xs e2) = do
  e1' <- toTermForDebug e1
  e2' <- toTermForDebug e2
  return $ TermSigmaElim e1' xs e2'
toTermForDebug (_ :< NeutIndex s) = return $ TermIndex s
toTermForDebug (meta :< NeutIndexIntro x) = return $ TermIndexIntro x meta
toTermForDebug (_ :< NeutIndexElim e branchList) = do
  e' <- toTermForDebug e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- toTermForDebug body
      return (l, body')
  return $ TermIndexElim e' branchList'
toTermForDebug (_ :< NeutConst x) = do
  undefined
toTermForDebug (_ :< NeutUniv j) = return $ TermUniv j
toTermForDebug (_ :< NeutMu s e) = do
  e' <- toTermForDebug e
  return $ TermMu s e'
toTermForDebug (_ :< NeutHole x) = return $ TermVar $ "HOLE" ++ x
