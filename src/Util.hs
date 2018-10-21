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

import Debug.Trace

toPiIntroSeq :: Neut -> (Neut, [(Identifier, Neut, Identifier)])
toPiIntroSeq (meta :< NeutPiIntro (x, t) body) = do
  let (body', args) = toPiIntroSeq body
  (body', (x, t, meta) : args)
toPiIntroSeq t = (t, [])

fromPiIntroSeq :: (Neut, [(Identifier, Neut, Identifier)]) -> Neut
fromPiIntroSeq (e, []) = e
fromPiIntroSeq (e, (x, t, meta):rest) = do
  let e' = fromPiIntroSeq (e, rest)
  meta :< NeutPiIntro (x, t) e'
  -- fromPiIntroSeq (meta :< NeutPiIntro (x, t) e, rest)

toPiElimSeq :: Neut -> (Neut, [(Identifier, Neut)])
toPiElimSeq (i :< NeutPiElim e1 e2) = do
  let (fun, xs) = toPiElimSeq e1
  (fun, (i, e2) : xs)
toPiElimSeq c = (c, [])

fromPiElimSeq :: (Neut, [(Identifier, Neut)]) -> Neut
fromPiElimSeq (term, []) = term
fromPiElimSeq (term, (i, v):xs) = fromPiElimSeq (i :< NeutPiElim term v, xs)

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

var :: Neut -> [Identifier]
var e = fst $ varAndHole e

nonLinear :: Neut -> [Identifier]
nonLinear (_ :< NeutVar _) = []
nonLinear (_ :< NeutConst _ _) = []
nonLinear (_ :< NeutPi (x, tdom) tcod) = do
  let ns1 = nonLinear tdom
  let ns2 = isAffine x $ nonLinear tcod
  ns1 ++ ns2
nonLinear (_ :< NeutPiIntro (x, _) e) = isAffine x (var e) ++ nonLinear e
nonLinear (_ :< NeutPiElim e1 e2) = do
  let ns1 = nonLinear e1
  let ns2 = nonLinear e2
  ns1 ++ ns2
nonLinear (_ :< NeutSigma [] t2) = nonLinear t2
nonLinear (i :< NeutSigma ((x, t):xts) t2) = do
  let ns1 = nonLinear (i :< NeutSigma xts t2)
  let ns2 = nonLinear t
  let vs = join $ map var (map snd xts ++ [t2])
  isAffine x vs ++ ns1 ++ ns2
nonLinear (_ :< NeutSigmaIntro es) = join $ map nonLinear es
nonLinear (_ :< NeutSigmaElim e1 xs e2) = do
  let ns1 = nonLinear e1
  let ns2 = nonLinear e2
  let vs = var e2
  let tmp = concatMap (`isLinear` vs) xs
  tmp ++ ns1 ++ ns2
nonLinear (_ :< NeutBox e) = nonLinear e
nonLinear (_ :< NeutBoxIntro e) = nonLinear e
nonLinear (_ :< NeutBoxElim e) = nonLinear e
nonLinear (_ :< NeutIndex _) = []
nonLinear (_ :< NeutIndexIntro _) = []
nonLinear (_ :< NeutIndexElim e branchList) = do
  let vs = nonLinear e
  let (_, es) = unzip branchList
  let vss = map nonLinear es
  vs ++ join vss
nonLinear (_ :< NeutUniv _) = []
nonLinear (_ :< NeutMu s e) = isLinear s (var e) ++ nonLinear e
nonLinear (_ :< NeutHole _) = []

varAndHole :: Neut -> ([Identifier], [Identifier])
varAndHole (_ :< NeutVar s) = ([s], [])
varAndHole (_ :< NeutConst _ _) = ([], [])
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
varAndHole (_ :< NeutSigma xts t2) = do
  let (xs, ts) = unzip xts
  let (vs1, vs2) = pairwiseConcat $ map varAndHole (t2 : ts)
  (filter (`notElem` xs) vs1, vs2)
varAndHole (_ :< NeutSigmaIntro es) = pairwiseConcat $ map varAndHole es
varAndHole (_ :< NeutSigmaElim e1 xs e2) = do
  let vs1 = varAndHole e1
  let (vs21, vs22) = varAndHole e2
  let vs2 = (filter (`notElem` xs) vs21, vs22)
  pairwiseConcat [vs1, vs2]
varAndHole (_ :< NeutBox e) = varAndHole e
varAndHole (_ :< NeutBoxIntro e) = varAndHole e
varAndHole (_ :< NeutBoxElim e) = varAndHole e
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
varAndHole (_ :< NeutUniv _) = ([], [])
varAndHole (_ :< NeutMu _ e) = varAndHole e
varAndHole (_ :< NeutHole x) = ([], [x])

varPos :: Pos -> [Identifier]
varPos (PosVar s) = [s]
varPos (PosConst _) = []
varPos (PosSigma xts t2) = do
  let (xs, ts) = unzip xts
  let vs = concatMap varPos (t2 : ts)
  filter (`notElem` xs) vs
varPos (PosSigmaIntro es) = concatMap varPos es
varPos (PosBox e) = varNeg e
varPos (PosBoxIntro e) = varNeg e
varPos (PosIndex _) = []
varPos (PosIndexIntro _) = []
varPos (PosDown e) = varNeg e
varPos (PosDownIntro e) = varNeg e
varPos PosUniv = []
varPos (PosArith _ e1 e2) = varPos e1 ++ varPos e2

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
varNeg (NegBoxElim e) = varPos e
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
varNeg (NegPrint _ e) = varPos e

varIndex :: Index -> [Identifier]
varIndex (IndexLabel x) = [x]
varIndex _ = []

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
  t <- lookupTypeEnv' i >>= reduce
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
  boxMeta <- newNameWith "meta"
  l <- newName
  return $ boxMeta :< NeutBox (univMeta :< NeutUniv (UnivLevelHole l))

lookupTypeEnv'' :: String -> WithEnv Neut
lookupTypeEnv'' s = do
  mt <- gets (lookup s . typeEnv)
  case mt of
    Just t -> return t
    Nothing -> boxUniv

depends :: Justification -> Justification -> Bool
depends j1 j2 = do
  let vs1 = varInJusitifcation j1
  let vs2 = varInJusitifcation j2
  foldr (\x -> (||) (x `elem` vs2)) False vs1

varInJusitifcation :: Justification -> [Identifier]
varInJusitifcation (Asserted i) = [i]
varInJusitifcation (Assumption i) = [i]
varInJusitifcation (Join js) = concatMap varInJusitifcation js

toVar :: Identifier -> WithEnv Neut
toVar x = do
  t <- lookupTypeEnv' x
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutVar x

toConst :: Identifier -> WithEnv Neut
toConst x = do
  t <- lookupTypeEnv' x
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutConst x t

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
