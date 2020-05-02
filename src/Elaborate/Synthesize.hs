module Elaborate.Synthesize
  ( synthesize,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Constraint
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.List (nub, sortOn)
import Data.Log
import Data.Meta
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Analyze

-- Given a queue of constraints (easier ones comes earlier), try to synthesize
-- all of them using heuristics.
synthesize :: WithEnv ()
synthesize = do
  q <- gets constraintQueue
  sub <- gets substEnv
  case Q.getMin q of
    Nothing ->
      return ()
    Just (Enriched (e1, e2) hs _)
      | Just (h, e) <- lookupAny (S.toList hs) sub ->
        resolveStuck e1 e2 h e
    Just (Enriched _ _ (ConstraintQuasiPattern m ess e)) ->
      resolvePiElim m ess e
    Just (Enriched _ _ (ConstraintFlexRigid m ess e)) ->
      resolvePiElim m ess e
    _ ->
      throwTypeErrors

resolveStuck ::
  WeakTermPlus -> WeakTermPlus -> Ident -> WeakTermPlus -> WithEnv ()
resolveStuck e1 e2 h e = do
  let s = IntMap.singleton (asInt h) e
  let e1' = substWeakTermPlus s e1
  let e2' = substWeakTermPlus s e2
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
resolvePiElim :: Ident -> [[WeakTermPlus]] -> WeakTermPlus -> WithEnv ()
resolvePiElim h ess e = do
  let lengthInfo = map length ess
  let es = concat ess
  xss <- toVarList (varWeakTermPlus e) es >>= toAltList
  let xsss = map (takeByCount lengthInfo) xss
  let lamList = map (bindFormalArgs e) xsss
  deleteMin
  tryPlanList (metaOf e) $ map (resolveIdent h) lamList

resolveIdent :: Ident -> WeakTermPlus -> WithEnv ()
resolveIdent h@(I (_, i)) e = do
  modify (\env -> env {substEnv = IntMap.insert i e (substEnv env)})
  q <- gets constraintQueue
  let (q1, q2) = Q.partition (\(Enriched _ hs _) -> h `elem` hs) q
  let q1' = Q.mapU asAnalyzable q1
  modify (\env -> env {constraintQueue = q1' `Q.union` q2})
  synthesize

asAnalyzable :: EnrichedConstraint -> EnrichedConstraint
asAnalyzable (Enriched cs hs _) =
  Enriched cs hs ConstraintAnalyzable

-- Try the list of alternatives.
tryPlanList :: Meta -> [WithEnv a] -> WithEnv a
tryPlanList m planList =
  case planList of
    [] ->
      raiseError m "cannot synthesize(tryPlanList)."
    [plan] ->
      plan
    plan : rest ->
      catch plan (\(_ :: Error) -> tryPlanList m rest)

deleteMin :: WithEnv ()
deleteMin =
  modify (\env -> env {constraintQueue = Q.deleteMin (constraintQueue env)})

-- [x, x, y, z, z] ~>
--   [ [x, p, y, z, q]
--   , [x, p, y, q, z]
--   , [p, x, y, z, q]
--   , [p, x, y, q, z]
--   ]
-- (p, q : fresh variables)
toAltList :: [WeakIdentPlus] -> WithEnv [[WeakIdentPlus]]
toAltList xts = do
  let xs = map (\(_, x, _) -> x) xts
  mapM (discardInactive xts) $ chooseActive $ toIndexInfo xs

-- [x, x, y, z, z] ~> [(x, [0, 1]), (y, [2]), (z, [3, 4])]
toIndexInfo :: Eq a => [a] -> [(a, [Int])]
toIndexInfo xs =
  toIndexInfo' $ zip xs [0 ..]

toIndexInfo' :: Eq a => [(a, Int)] -> [(a, [Int])]
toIndexInfo' input =
  case input of
    [] ->
      []
    ((x, i) : xs) -> do
      let (is, xs') = toIndexInfo'' x xs
      let xs'' = toIndexInfo' xs'
      (x, i : is) : xs''

toIndexInfo'' :: Eq a => a -> [(a, Int)] -> ([Int], [(a, Int)])
toIndexInfo'' x info =
  case info of
    [] ->
      ([], [])
    ((y, i) : ys) -> do
      let (is, ys') = toIndexInfo'' x ys
      if x == y
        then (i : is, ys') -- remove x from the list
        else (is, (y, i) : ys')

chooseActive :: [(Ident, [Int])] -> [[(Ident, Int)]]
chooseActive xs =
  pickup $ map (\(x, is) -> zip (repeat x) is) xs

pickup :: Eq a => [[a]] -> [[a]]
pickup input =
  case input of
    [] ->
      [[]]
    (xs : xss) -> do
      let yss = pickup xss
      x <- xs
      map (x :) yss

discardInactive :: [WeakIdentPlus] -> [(Ident, Int)] -> WithEnv [WeakIdentPlus]
discardInactive xs indexList =
  forM (zip xs [0 ..]) $ \((mx, x, t), i) ->
    case lookup x indexList of
      Just j
        | i == j ->
          return (mx, x, t)
      _ -> do
        y <- newNameWith' "hole"
        return (mx, y, t)

-- takeByCount [1, 3, 2] [a, b, c, d, e, f, g, h] ~> [[a], [b, c, d], [e, f]]
takeByCount :: [Int] -> [a] -> [[a]]
takeByCount idxList xs =
  case idxList of
    [] ->
      []
    i : is -> do
      let ys = take i xs
      let yss = takeByCount is (drop i xs)
      ys : yss

throwTypeErrors :: WithEnv ()
throwTypeErrors = do
  q <- gets constraintQueue
  let pcs = sortOn fst $ nub $ setupPosInfo $ Q.toList q
  errorList <- constructErrors [] pcs
  throw $ ErrorRight errorList

setupPosInfo :: [EnrichedConstraint] -> [(PosInfo, PreConstraint)]
setupPosInfo constraintList =
  case constraintList of
    [] ->
      []
    Enriched (e1, e2) _ _ : cs -> do
      let pos1 = getPosInfo $ metaOf e1
      let pos2 = getPosInfo $ metaOf e2
      case snd pos1 `compare` snd pos2 of
        LT ->
          (pos2, (e2, e1)) : setupPosInfo cs
        _ ->
          (pos1, (e1, e2)) : setupPosInfo cs

constructErrors :: [PosInfo] -> [(PosInfo, PreConstraint)] -> WithEnv [Log]
constructErrors ps info =
  case info of
    [] ->
      return []
    (pos, (e1, e2)) : pcs -> do
      e1' <- unravel e1
      e2' <- unravel e2
      let msg = constructErrorMsg e1' e2'
      as <- constructErrors (pos : ps) pcs
      return $ logError pos msg : as

constructErrorMsg :: WeakTermPlus -> WeakTermPlus -> T.Text
constructErrorMsg e1 e2 =
  "couldn't verify the definitional equality of the following two terms:\n- "
    <> toText e1
    <> "\n- "
    <> toText e2

unravel :: WeakTermPlus -> WithEnv WeakTermPlus
unravel term =
  case term of
    (m, WeakTermTau) ->
      return (m, WeakTermTau)
    (m, WeakTermUpsilon x) -> do
      x' <- unravelUpsilon x
      return (m, WeakTermUpsilon x')
    (m, WeakTermPi xts t) -> do
      (xts', t') <- unravelBinder xts t
      return (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro xts e) -> do
      (xts', e') <- unravelBinder xts e
      return (m, WeakTermPiIntro xts' e')
    (m, WeakTermPiElim e es) -> do
      e' <- unravel e
      es' <- mapM unravel es
      return (m, WeakTermPiElim e' es')
    (m, WeakTermFix (mx, x, t) xts e) -> do
      x' <- unravelUpsilon x
      (xts', e') <- unravelBinder xts e
      return (m, WeakTermFix (mx, x', t) xts' e')
    (m, WeakTermConst x) ->
      return (m, WeakTermConst x)
    (m, WeakTermCall x) ->
      return (m, WeakTermCall x)
    (m, WeakTermHole h) -> do
      h' <- unravelHole h
      return (m, WeakTermHole h')
    (m, WeakTermInt t x) ->
      return (m, WeakTermInt t x)
    (m, WeakTermFloat t x) ->
      return (m, WeakTermFloat t x)
    (m, WeakTermEnum s) ->
      return (m, WeakTermEnum s)
    (m, WeakTermEnumIntro x) ->
      return (m, WeakTermEnumIntro x)
    (m, WeakTermEnumElim (e, t) caseList) -> do
      e' <- unravel e
      caseList' <- unravelCaseList caseList
      return (m, WeakTermEnumElim (e', t) caseList')
    (m, WeakTermArray dom kind) -> do
      dom' <- unravel dom
      return (m, WeakTermArray dom' kind)
    (m, WeakTermArrayIntro kind es) -> do
      es' <- mapM unravel es
      return (m, WeakTermArrayIntro kind es')
    (m, WeakTermArrayElim kind xts e1 e2) -> do
      e1' <- unravel e1
      (xts', e2') <- unravelBinder xts e2
      return (m, WeakTermArrayElim kind xts' e1' e2')
    (m, WeakTermStruct ts) -> return (m, WeakTermStruct ts)
    (m, WeakTermStructIntro ets) -> do
      let (es, ts) = unzip ets
      es' <- mapM unravel es
      return (m, WeakTermStructIntro $ zip es' ts)
    (m, WeakTermStructElim xts e1 e2) -> do
      e1' <- unravel e1
      (xts', e2') <- unravelStruct xts e2
      return (m, WeakTermStructElim xts' e1' e2')
    (_, WeakTermQuestion e _) ->
      unravel e
    (_, WeakTermErase _ e) ->
      unravel e

unravelUpsilon :: Ident -> WithEnv Ident
unravelUpsilon (I (s, i)) = do
  nenv <- gets nameEnv
  case Map.lookup s nenv of
    Just s' ->
      return $ I (s', i)
    Nothing -> do
      j <- newCountPP
      let s' = T.pack $ "var" ++ show j
      modify (\e -> e {nameEnv = Map.insert s s' nenv})
      return $ I (s', i)

unravelHole :: Ident -> WithEnv Ident
unravelHole (I (s, i)) = do
  rnenv <- gets revNameEnv
  case IntMap.lookup i rnenv of
    Just j ->
      return $ I (s, j)
    Nothing -> do
      j <- newCountPP
      modify (\env -> env {revNameEnv = IntMap.insert i j rnenv})
      return $ I (s, j)

unravelBinder ::
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], WeakTermPlus)
unravelBinder binder e =
  case binder of
    [] -> do
      e' <- unravel e
      return ([], e')
    (mx, x, t) : xts -> do
      t' <- unravel t
      x' <- unravelUpsilon x
      (xts', e') <- unravelBinder xts e
      return ((mx, x', t') : xts', e')

unravelCaseList :: [(EnumCasePlus, WeakTermPlus)] -> WithEnv [(EnumCasePlus, WeakTermPlus)]
unravelCaseList caseList = do
  let (ls, es) = unzip caseList
  es' <- mapM unravel es
  return $ zip ls es'

unravelStruct ::
  [(Meta, Ident, a)] ->
  WeakTermPlus ->
  WithEnv ([(Meta, Ident, a)], WeakTermPlus)
unravelStruct binder e =
  case binder of
    [] -> do
      e' <- unravel e
      return ([], e')
    (mx, x, t) : xts -> do
      x' <- unravelUpsilon x
      (xts', e') <- unravelStruct xts e
      return ((mx, x', t) : xts', e')
