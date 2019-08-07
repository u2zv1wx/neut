module Elaborate.Synthesize
  ( synthesize
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.PQueue.Min        as Q

import           Data.Basic
import           Data.Constraint
import           Data.Env
import           Data.WeakTerm
import           Elaborate.Analyze

-- Given a queue of constraints (easier ones comes earlier), try to synthesize
-- all of them using heuristics.
synthesize :: ConstraintQueue -> WithEnv ()
synthesize q = do
  sub <- gets substEnv
  case Q.getMin q of
    Nothing -> return ()
    Just (Enriched (e1, e2) ms _)
      | Just (m, e) <- lookupAny ms sub -> resolveStuck q e1 e2 m e
    Just (Enriched _ _ (ConstraintImmediate m e)) -> resolveHole q m e
    Just (Enriched _ _ (ConstraintPattern i m es e)) -> resolvePiElim q i m es e
    Just (Enriched _ _ (ConstraintQuasiPattern i m es e)) ->
      resolvePiElim q i m es e
    Just (Enriched _ _ (ConstraintFlexRigid i m es e)) ->
      resolvePiElim q i m es e
    Just (Enriched _ _ (ConstraintFlexFlex i m es e)) ->
      resolvePiElim q i m es e
    Just _ -> throwError "cannot synthesize(synth)"

resolveStuck ::
     ConstraintQueue -> WeakTerm -> WeakTerm -> Hole -> WeakTerm -> WithEnv ()
resolveStuck q e1 e2 (h, i) e = do
  let e1' = substWeakTerm [(h, shiftWeakTerm i e)] e1
  let e2' = substWeakTerm [(h, shiftWeakTerm i e)] e2
  cs <- simp [(e1', e2')]
  synthesize $ Q.deleteMin q `Q.union` Q.fromList cs

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
     ConstraintQueue
  -> WeakLevel
  -> Hole
  -> [WeakTerm]
  -> WeakTerm
  -> WithEnv ()
resolvePiElim q i m es e = do
  xs <- toVarList es
  xss <- toAltList xs
  lamList <- mapM (bindFormalArgs i e) xss
  chain q $ flip map lamList $ \lam -> resolveHole q m lam

-- ?M^{+k} = e ~~> ?M = e^{-k}
resolveHole :: ConstraintQueue -> Hole -> WeakTerm -> WithEnv ()
resolveHole q (h, i) e = do
  let e' = shiftWeakTerm (WeakLevelNegate i) e
  modify (\env -> env {substEnv = compose [(h, e')] (substEnv env)})
  let rest = Q.deleteMin q
  let (q1, q2) = Q.partition (\(Enriched _ ms _) -> h `elem` map fst ms) rest
  synthesize q1
  synthesize q2

-- [e, x, y, y, e2, e3, z] ~> [p, x, y, y, q, r, z]  (p, q, r: new variables)
toVarList :: [WeakTerm] -> WithEnv [Identifier]
toVarList [] = return []
toVarList ((_ :< WeakTermUpsilon x):es) = do
  xs <- toVarList es
  return $ x : xs
toVarList (_:es) = do
  x <- newNameWith "hole"
  xs <- toVarList es
  return $ x : xs

-- [x, x, y, z, z] ~>
--   [ [x, p, y, z, q]
--   , [x, p, y, q, z]
--   , [p, x, y, z, q]
--   , [p, x, y, q, z]
--   ]
-- (p, q : fresh variables)
toAltList :: [Identifier] -> WithEnv [[Identifier]]
toAltList xs = mapM (discardInactive xs) $ chooseActive $ toIndexInfo xs

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

discardInactive :: [Identifier] -> [(Identifier, Int)] -> WithEnv [Identifier]
discardInactive xs indexList =
  forM (zip xs [0 ..]) $ \(x, i) ->
    case lookup x indexList of
      Just j
        | i == j -> return x
      _ -> newNameWith "hole"

-- Try the list of alternatives.
chain :: ConstraintQueue -> [WithEnv a] -> WithEnv a
chain _ []     = throwError "cannot synthesize(chain)"
chain c (e:es) = e `catchError` const (chain c es)

lookupAny :: [Hole] -> [(Identifier, a)] -> Maybe (Hole, a)
lookupAny [] _ = Nothing
lookupAny ((h, i):ks) sub =
  case lookup h sub of
    Just v  -> Just ((h, i), v)
    Nothing -> lookupAny ks sub

bindFormalArgs :: WeakLevel -> WeakTerm -> [Identifier] -> WithEnv WeakTerm
bindFormalArgs i e xs = do
  ts <- mapM (const newHole) xs
  meta <- newNameWith "meta"
  return $ meta :< WeakTermPiIntro i (zip xs ts) e
