{-# LANGUAGE OverloadedStrings #-}

module Elaborate.Synthesize
  ( synthesize
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List (nub, sortOn)

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Basic
import Data.Constraint
import Data.Env
import Data.Log
import Data.WeakTerm
import Elaborate.Analyze

-- Given a queue of constraints (easier ones comes earlier), try to synthesize
-- all of them using heuristics.
synthesize :: WithEnv ()
synthesize = do
  q <- gets constraintQueue
  sub <- gets substEnv
  case Q.getMin q of
    Nothing -> return ()
    Just (Enriched (e1, e2) hs _)
      | Just (h, e) <- lookupAny (S.toList hs) sub -> resolveStuck e1 e2 h e
    Just (Enriched _ _ (ConstraintQuasiPattern m ess e)) -> do
      resolvePiElim m ess e
    Just (Enriched _ _ (ConstraintFlexRigid m ess e)) -> do
      resolvePiElim m ess e
    Just (Enriched _ _ _) -> do
      resolveOther $ Q.toList q

-- e1だけがstuckしているとき、e2だけがstuckしているとき、両方がstuckしているときをそれぞれ
-- 独立したケースとして扱えるようにしたほうがよい（そうすればsubstを減らせる）
-- つまり、e1とe2のstuck reasonをそれぞれ別々に保持したほうがよい。
-- synthのときにlookupAnyできるかでseparateするとか？
resolveStuck ::
     WeakTermPlus -> WeakTermPlus -> Identifier -> WeakTermPlus -> WithEnv ()
resolveStuck e1 e2 h e = do
  let e1' = substWeakTermPlus [(h, e)] e1
  let e2' = substWeakTermPlus [(h, e)] e2
  deleteMin
  simp [(e1', e2')]
  synthesize

-- synthesize `hole @ arg-1 @ ... @ arg-n = e`, where arg-i is a variable.
-- Suppose that we received a quasi-pattern ?M @ x @ x @ y @ z == e.
-- What this function do is to try two alternatives in this case:
--   (1) ?M == lam x. lam _. lam y. lam z. e
--   (2) ?M == lam _. lam x. lam y. lam z. e
-- where `_` are new variables. In other words, this function tries
-- all the alternatives that are obtained by choosing one `x` from the
-- list [x, x, y, z], replacing all the other occurrences of `x` with new variables.
-- If the given pattern is a flex-rigid pattern like ?M @ x @ x @ e1 @ y == e,
-- this function replaces all the arguments that are not variable by
-- fresh variables, and try to resolve the new quasi-pattern ?M @ x @ x @ z @ y == e.
resolvePiElim :: Identifier -> [[WeakTermPlus]] -> WeakTermPlus -> WithEnv ()
resolvePiElim h ess e = do
  let lengthInfo = map length ess
  let es = concat ess
  xss <- toVarList (varWeakTermPlus e) es >>= toAltList
  let xsss = map (takeByCount lengthInfo) xss
  let lamList = map (bindFormalArgs e) xsss
  deleteMin
  tryPlanList (metaOf e) $ map (resolveIdentifier h) lamList

resolveIdentifier :: Identifier -> WeakTermPlus -> WithEnv ()
resolveIdentifier h@(I (_, i)) e = do
  modify (\env -> env {substEnv = IntMap.insert i e (substEnv env)})
  q <- gets constraintQueue
  let (q1, q2) = Q.partition (\(Enriched _ hs _) -> h `elem` hs) q
  let q1' = Q.mapU asAnalyzable q1
  modify (\env -> env {constraintQueue = q1' `Q.union` q2})
  synthesize

resolveOther :: [EnrichedConstraint] -> WithEnv ()
resolveOther [] = throwTypeErrors
resolveOther ((Enriched (e1, e2) fmvs _):cs) = do
  sub <- gets substEnv
  case lookupAny (S.toList fmvs) sub of
    Just (h, e) -> resolveStuck e1 e2 h e
    Nothing -> resolveOther cs

asAnalyzable :: EnrichedConstraint -> EnrichedConstraint
asAnalyzable (Enriched cs ms _) = Enriched cs ms ConstraintAnalyzable

-- Try the list of alternatives.
tryPlanList :: Meta -> [WithEnv a] -> WithEnv a
tryPlanList m [] = raiseError m $ "cannot synthesize(tryPlanList)."
tryPlanList _ [plan] = plan
tryPlanList m (plan:planList) = catchError plan (const $ tryPlanList m planList)

deleteMin :: WithEnv ()
deleteMin = do
  modify (\env -> env {constraintQueue = Q.deleteMin (constraintQueue env)})

-- [x, x, y, z, z] ~>
--   [ [x, p, y, z, q]
--   , [x, p, y, q, z]
--   , [p, x, y, z, q]
--   , [p, x, y, q, z]
--   ]
-- (p, q : fresh variables)
-- {} toAltList {それぞれのlistはlinear list}
toAltList :: [IdentifierPlus] -> WithEnv [[IdentifierPlus]]
toAltList xts = do
  let xs = map (\(_, x, _) -> x) xts
  result <- mapM (discardInactive xts) $ chooseActive $ toIndexInfo xs
  return result

-- [x, x, y, z, z] ~> [(x, [0, 1]), (y, [2]), (z, [3, 4])]
toIndexInfo :: Eq a => [a] -> [(a, [Int])]
toIndexInfo xs = toIndexInfo' $ zip xs [0 ..]

toIndexInfo' :: Eq a => [(a, Int)] -> [(a, [Int])]
toIndexInfo' [] = []
toIndexInfo' ((x, i):xs) = do
  let (is, xs') = toIndexInfo'' x xs
  let xs'' = toIndexInfo' xs'
  (x, i : is) : xs''

toIndexInfo'' :: Eq a => a -> [(a, Int)] -> ([Int], [(a, Int)])
toIndexInfo'' _ [] = ([], [])
toIndexInfo'' x ((y, i):ys) = do
  let (is, ys') = toIndexInfo'' x ys
  if x == y
    then (i : is, ys') -- remove x from the list
    else (is, (y, i) : ys')

chooseActive :: [(Identifier, [Int])] -> [[(Identifier, Int)]]
chooseActive xs = do
  let xs' = map (\(x, is) -> zip (repeat x) is) xs
  pickup xs'

pickup :: Eq a => [[a]] -> [[a]]
pickup [] = [[]]
pickup (xs:xss) = do
  let yss = pickup xss
  x <- xs
  map (\ys -> x : ys) yss

discardInactive ::
     [IdentifierPlus] -> [(Identifier, Int)] -> WithEnv [IdentifierPlus]
discardInactive xs indexList =
  forM (zip xs [0 ..]) $ \((mx, x, t), i) ->
    case lookup x indexList of
      Just j
        | i == j -> return (mx, x, t)
      _ -> do
        y <- newNameWith' "hole"
        return (mx, y, t)

-- takeByCount [1, 3, 2] [a, b, c, d, e, f, g, h] ~> [[a], [b, c, d], [e, f]]
takeByCount :: [Int] -> [a] -> [[a]]
takeByCount [] _ = []
takeByCount (i:is) xs = do
  let ys = take i xs
  let yss = takeByCount is (drop i xs)
  ys : yss

throwTypeErrors :: WithEnv ()
throwTypeErrors = do
  q <- gets constraintQueue
  let pcs = sortOn fst $ nub $ setupPosInfo $ Q.toList q
  errorList <- constructErrors [] pcs
  throwError errorList

setupPosInfo :: [EnrichedConstraint] -> [(PosInfo, PreConstraint)]
setupPosInfo [] = []
setupPosInfo ((Enriched (e1, e2) _ _):cs) = do
  let pos1 = getPosInfo $ metaOf e1
  let pos2 = getPosInfo $ metaOf e2
  case snd pos1 `compare` snd pos2 of
    LT -> (pos2, (e2, e1)) : setupPosInfo cs
    _ -> (pos1, (e1, e2)) : setupPosInfo cs

constructErrors :: [PosInfo] -> [(PosInfo, PreConstraint)] -> WithEnv [Log]
constructErrors _ [] = return []
constructErrors ps ((pos, (e1, e2)):pcs) = do
  e1' <- unravel e1
  e2' <- unravel e2
  let msg = constructErrorMsg e1' e2'
  as <- constructErrors (pos : ps) pcs
  return $ logError pos msg : as

constructErrorMsg :: WeakTermPlus -> WeakTermPlus -> T.Text
constructErrorMsg e1 e2 =
  "couldn't verify the definitional equality of the following two terms:\n- " <>
  toText e1 <> "\n- " <> toText e2

unravel :: WeakTermPlus -> WithEnv WeakTermPlus
unravel (m, WeakTermTau) = return (m, WeakTermTau)
unravel (m, WeakTermUpsilon x) = do
  x' <- unravelUpsilon x
  return (m, WeakTermUpsilon x')
unravel (m, WeakTermPi mName xts t) = do
  (xts', t') <- unravelBinder xts t
  return (m, WeakTermPi mName xts' t')
unravel (m, WeakTermPiIntro xts e) = do
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermPiIntro xts' e')
unravel (m, WeakTermPiIntroNoReduce xts e) = do
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermPiIntroNoReduce xts' e')
-- the "content" of this term is not used in toText, and so there's no need to unravel this term
unravel (m, WeakTermPiIntroPlus ind (name, is, args1, args2) xts e) =
  return (m, WeakTermPiIntroPlus ind (name, is, args1, args2) xts e)
unravel (m, WeakTermPiElim e es) = do
  e' <- unravel e
  es' <- mapM unravel es
  return (m, WeakTermPiElim e' es')
unravel (m, WeakTermIter (mx, x, t) xts e) = do
  x' <- unravelUpsilon x
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermIter (mx, x', t) xts' e')
unravel (m, WeakTermConst x) = return (m, WeakTermConst x)
unravel (m, WeakTermZeta h) = do
  h' <- unravelZeta h
  return (m, WeakTermZeta h')
unravel (m, WeakTermInt t x) = do
  return (m, WeakTermInt t x)
unravel (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
unravel (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
unravel (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
unravel (m, WeakTermFloat t x) = do
  return (m, WeakTermFloat t x)
unravel (m, WeakTermEnum s) = return (m, WeakTermEnum s)
unravel (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
unravel (m, WeakTermEnumElim (e, t) caseList) = do
  e' <- unravel e
  caseList' <- unravelCaseList caseList
  return (m, WeakTermEnumElim (e', t) caseList')
unravel (m, WeakTermArray dom kind) = do
  dom' <- unravel dom
  return (m, WeakTermArray dom' kind)
unravel (m, WeakTermArrayIntro kind es) = do
  es' <- mapM unravel es
  return (m, WeakTermArrayIntro kind es')
unravel (m, WeakTermArrayElim kind xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelBinder xts e2
  return (m, WeakTermArrayElim kind xts' e1' e2')
unravel (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
unravel (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM unravel es
  return (m, WeakTermStructIntro $ zip es' ts)
unravel (m, WeakTermStructElim xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelStruct xts e2
  return (m, WeakTermStructElim xts' e1' e2')
unravel (m, WeakTermCase indName e cxtes) = do
  e' <- unravel e
  cxtes' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      (xts', body') <- unravelBinder xts body
      return ((c, xts'), body')
  return (m, WeakTermCase indName e' cxtes')
unravel (_, WeakTermWithNote e _) = unravel e

unravelUpsilon :: Identifier -> WithEnv Identifier
unravelUpsilon (I (s, i)) = do
  nenv <- gets nameEnv
  case Map.lookup s nenv of
    Just s' -> return $ I (s', i)
    Nothing -> do
      j <- newCountPP
      let s' = T.pack $ "var" ++ show j
      modify (\e -> e {nameEnv = Map.insert s s' nenv})
      return $ I (s', i)

unravelZeta :: Identifier -> WithEnv Identifier
unravelZeta (I (s, i)) = do
  rnenv <- gets revNameEnv
  case IntMap.lookup i rnenv of
    Just j -> return $ I (s, j)
    Nothing -> do
      j <- newCountPP
      modify (\env -> env {revNameEnv = IntMap.insert i j rnenv})
      return $ I (s, j)

unravelBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
unravelBinder [] e = do
  e' <- unravel e
  return ([], e')
unravelBinder ((mx, x, t):xts) e = do
  t' <- unravel t
  x' <- unravelUpsilon x
  (xts', e') <- unravelBinder xts e
  return ((mx, x', t') : xts', e')

unravelCaseList ::
     [(WeakCasePlus, WeakTermPlus)] -> WithEnv [(WeakCasePlus, WeakTermPlus)]
unravelCaseList caseList = do
  let (ls, es) = unzip caseList
  ls' <- mapM unravelWeakCase ls
  es' <- mapM unravel es
  return $ zip ls' es'

unravelWeakCase :: WeakCasePlus -> WithEnv WeakCasePlus
unravelWeakCase (m, WeakCaseInt t a) = do
  t' <- unravel t
  return (m, WeakCaseInt t' a)
unravelWeakCase l = return l

unravelStruct ::
     [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Meta, Identifier, ArrayKind)], WeakTermPlus)
unravelStruct [] e = do
  e' <- unravel e
  return ([], e')
unravelStruct ((mx, x, t):xts) e = do
  x' <- unravelUpsilon x
  (xts', e') <- unravelStruct xts e
  return ((mx, x', t) : xts', e')
