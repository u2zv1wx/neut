module Elaborate.Synthesize
  ( synthesize,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Constraint
import Data.Env
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.List (nub, sortOn)
import Data.Log
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

resolveStuck :: WeakTermPlus -> WeakTermPlus -> Int -> WeakTermPlus -> WithEnv ()
resolveStuck e1 e2 h e = do
  let s = IntMap.singleton h e
  let e1' = substWeakTermPlus s e1
  let e2' = substWeakTermPlus s e2
  deleteMin
  simp [(e1', e2')]
  synthesize

-- synthesize `aster @ arg-1 @ ... @ arg-n = e`, where arg-i is a variable.
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
resolvePiElim :: Int -> [[WeakTermPlus]] -> WeakTermPlus -> WithEnv ()
resolvePiElim h ess e = do
  let lengthInfo = map length ess
  let es = concat ess
  xss <- toVarList (varWeakTermPlus e) es >>= toAltList
  let xsss = map (takeByCount lengthInfo) xss
  let lamList = map (bindFormalArgs e) xsss
  deleteMin
  tryPlanList (metaOf e) $ map (resolveIdent h) lamList

resolveIdent :: Int -> WeakTermPlus -> WithEnv ()
resolveIdent i e = do
  modify (\env -> env {substEnv = IntMap.insert i e (substEnv env)})
  q <- gets constraintQueue
  let (q1, q2) = Q.partition (\(Enriched _ hs _) -> i `elem` hs) q
  let q1' = Q.mapU asAnalyzable q1
  modify (\env -> env {constraintQueue = q1' `Q.union` q2})
  synthesize

asAnalyzable :: EnrichedConstraint -> EnrichedConstraint
asAnalyzable (Enriched cs hs _) =
  Enriched cs hs ConstraintAnalyzable

-- Try the list of alternatives.
tryPlanList :: Hint -> [WithEnv a] -> WithEnv a
tryPlanList m planList =
  case planList of
    [] ->
      raiseError m "cannot synthesize(tryPlanList)."
    [plan] ->
      plan
    plan : rest ->
      catch plan $ tryPlanList' m rest

tryPlanList' :: Hint -> [WithEnv a] -> Error -> WithEnv a
tryPlanList' m rest _ =
  tryPlanList m rest

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
        y <- newNameWith' "aster"
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
  throw $ Error errorList

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
      let msg = constructErrorMsg e1 e2
      as <- constructErrors (pos : ps) pcs
      return $ logError pos msg : as

constructErrorMsg :: WeakTermPlus -> WeakTermPlus -> T.Text
constructErrorMsg e1 e2 =
  "couldn't verify the definitional equality of the following two terms:\n- "
    <> toText e1
    <> "\n- "
    <> toText e2
