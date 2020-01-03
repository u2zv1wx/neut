module Elaborate.Synthesize
  ( synthesize
  ) where

import Control.Exception
import Control.Monad.Except
import Control.Monad.State

import qualified Data.PQueue.Min as Q
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Constraint
import Data.Env
import Data.PreTerm
import Elaborate.Analyze
import Elaborate.Infer (insWeakTypeEnv, metaTerminal, typeOf)
import Reduce.PreTerm

-- Given a queue of constraints (easier ones comes earlier), try to synthesize
-- all of them using heuristics.
synthesize :: ConstraintQueue -> WithEnv ()
synthesize q = do
  sub <- gets substEnv
  case Q.getMin q of
    Nothing -> return ()
    Just (Enriched (e1, e2) ms _)
      | Just (m, e) <- lookupAny ms sub -> resolveStuck q e1 e2 m e
    Just (Enriched _ _ (ConstraintPattern m ess e)) -> do
      resolvePiElim q m ess e
    Just (Enriched _ _ (ConstraintDelta x ess e)) -> do
      resolveDelta q x ess e
    Just (Enriched _ _ (ConstraintQuasiPattern m ess e)) -> do
      resolvePiElim q m ess e
    Just (Enriched _ _ (ConstraintFlexRigid m ess e)) -> do
      resolvePiElim q m ess e
    Just (Enriched (e1, e2) _ _) -> do
      throwError $ "cannot simplify:\n" ++ Pr.ppShow (e1, e2)

resolveStuck ::
     ConstraintQueue
  -> PreTermPlus
  -> PreTermPlus
  -> Hole
  -> PreTermPlus
  -> WithEnv ()
resolveStuck q e1 e2 h e = do
  let fmvs = holePreTermPlus e
  let e1' = substPreTermPlus [(h, e)] e1
  let e2' = substPreTermPlus [(h, e)] e2
  q' <- assert (h `notElem` fmvs) $ analyze [(e1', e2')]
  synthesize $ Q.deleteMin q `Q.union` q'

resolveDelta ::
     ConstraintQueue
  -> PreTermPlus
  -> [(PreMeta, [PreTermPlus])]
  -> PreTermPlus
  -> WithEnv ()
resolveDelta q body mess1 e2 = do
  q' <- analyze [(toPiElim body mess1, e2)]
  synthesize $ Q.deleteMin q `Q.union` q'

-- Synthesize `hole @ arg-1 @ ... @ arg-n = e`, where arg-i is a variable.
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
resolvePiElim ::
     ConstraintQueue -> Hole -> [[PreTermPlus]] -> PreTermPlus -> WithEnv ()
resolvePiElim q m ess e = do
  let fmvs = holePreTermPlus e
  let lengthInfo = assert (m `notElem` fmvs) $ map length ess
  let es = concat ess
  xss <- toVarList es >>= toAltList
  let xsss = map (takeByCount lengthInfo) xss
  let lamList = map (bindFormalArgs e) xsss
  chain q $ map (\lam -> resolveHole q m lam) lamList

-- resolveHoleは[(Hole, PreTermPlus)]を受け取るようにしたほうがよさそう。
-- で、synthesizeのときに複数のhole-substをまとめてこっちに渡す。
resolveHole :: ConstraintQueue -> Hole -> PreTermPlus -> WithEnv ()
resolveHole q m e = do
  senv <- gets substEnv
  e' <- reducePreTermPlus $ substPreTermPlus senv e
  modify (\env -> env {substEnv = compose [(m, e')] senv})
  let (q1, q2) = Q.partition (\(Enriched _ ms _) -> m `elem` ms) $ Q.deleteMin q
  let q1' = Q.mapU asAnalyzable q1
  synthesize $ q1' `Q.union` q2

asAnalyzable :: EnrichedConstraint -> EnrichedConstraint
asAnalyzable (Enriched cs ms _) = Enriched cs ms ConstraintAnalyzable

-- [e, x, y, y, e2, e3, z] ~> [p, x, y, y, q, r, z]  (p, q, r: new variables)
toVarList :: [PreTermPlus] -> WithEnv [(Identifier, PreTermPlus)]
toVarList [] = return []
toVarList (e@(_, PreTermUpsilon x):es) = do
  xts <- toVarList es
  let t = typeOf e
  return $ (x, t) : xts
toVarList (e:es) = do
  xts <- toVarList es
  x <- newNameWith "hole"
  let t = typeOf e
  insWeakTypeEnv x t
  return $ (x, t) : xts

-- [x, x, y, z, z] ~>
--   [ [x, p, y, z, q]
--   , [x, p, y, q, z]
--   , [p, x, y, z, q]
--   , [p, x, y, q, z]
--   ]
-- (p, q : fresh variables)
toAltList :: [IdentifierPlus] -> WithEnv [[IdentifierPlus]]
toAltList xts =
  mapM (discardInactive xts) $ chooseActive $ toIndexInfo (map fst xts)

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
  forM (zip xs [0 ..]) $ \((x, t), i) ->
    case lookup x indexList of
      Just j
        | i == j -> return (x, t)
      _ -> do
        y <- newNameWith "hole"
        insWeakTypeEnv y t
        return (y, t)

-- Try the list of alternatives.
chain :: ConstraintQueue -> [WithEnv a] -> WithEnv a
chain _ [] = throwError $ "cannot synthesize(chain)."
chain _ (e:_) = e

-- chain _ [e] = e
-- chain c (e:es) = catchError e $ (const $ chain c es)
lookupAny :: [Hole] -> [(Identifier, a)] -> Maybe (Hole, a)
lookupAny [] _ = Nothing
lookupAny (h:ks) sub = do
  case lookup h sub of
    Just v -> Just (h, v)
    _ -> lookupAny ks sub

bindFormalArgs :: PreTermPlus -> [[IdentifierPlus]] -> PreTermPlus
bindFormalArgs e [] = e
bindFormalArgs e (xts:xtss) = do
  let e' = bindFormalArgs e xtss
  let tPi = (metaTerminal, PreTermPi xts (typeOf e'))
  (PreMetaNonTerminal tPi Nothing, PreTermPiIntro xts e')

toPiElim :: PreTermPlus -> [(PreMeta, [PreTermPlus])] -> PreTermPlus
toPiElim e [] = e
toPiElim e ((m, es):ess) = toPiElim (m, PreTermPiElim e es) ess

-- takeByCount [1, 3, 2] [a, b, c, d, e, f, g, h] ~> [[a], [b, c, d], [e, f]]
takeByCount :: [Int] -> [a] -> [[a]]
takeByCount [] _ = []
takeByCount (i:is) xs = do
  let ys = take i xs
  let yss = takeByCount is (drop i xs)
  ys : yss
