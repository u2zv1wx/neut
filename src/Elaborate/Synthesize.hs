module Elaborate.Synthesize
  ( synthesize
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.PQueue.Min        as Q
import qualified Text.Show.Pretty       as Pr

import           Data.Basic
import           Data.Constraint
import           Data.Env
import           Data.WeakTerm
import           Elaborate.Analyze

-- Given a queue of constraints (easier ones comes earlier), try to synthesize
-- all of them using heuristics.
synthesize :: Q.MinQueue EnrichedConstraint -> WithEnv ()
synthesize q = do
  sub <- gets substEnv
  case Q.getMin q of
    Nothing -> return ()
    Just (Enriched (e1, e2) ms _)
      | Just (m, e) <- lookupAny ms sub -> resolveStuck q e1 e2 m e
    Just (Enriched _ _ (ConstraintPattern s m es e)) -> resolvePiElim q s m es e
    Just (Enriched _ _ (ConstraintQuasiPattern s m es e)) ->
      resolvePiElim q s m es e
    Just (Enriched _ _ (ConstraintFlexRigid s m es e)) ->
      resolvePiElim q s m es e
    Just (Enriched _ _ (ConstraintFlexFlex s m es e)) ->
      resolvePiElim q s m es e
    Just _ -> throwError "cannot synthesize(synth)"

resolveStuck ::
     Q.MinQueue EnrichedConstraint
  -> WeakTerm
  -> WeakTerm
  -> Identifier
  -> WeakTerm
  -> WithEnv ()
resolveStuck q e1 e2 m e = do
  let e1' = substWeakTerm [(m, e)] e1
  let e2' = substWeakTerm [(m, e)] e2
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
     Q.MinQueue EnrichedConstraint
  -> WeakTerm
  -> Identifier
  -> [WeakTerm]
  -> WeakTerm
  -> WithEnv ()
resolvePiElim q s m es e = do
  xs <- forceVarList es
  xss <- toAltList xs
  lamList <- mapM (\ys -> bindFormalArgs s ys e) xss
  chain q $
    flip map lamList $ \lam -> do
      modify (\env -> env {substEnv = compose [(m, lam)] (substEnv env)})
      let current = Q.deleteMin q
      let (q1, q2) = Q.partition (\(Enriched _ ms _) -> m `elem` ms) current
      synthesize q1
      synthesize q2

-- [e, x, y, y, e2, e3, z] ~> [p, x, y, y, q, r, z]  (p, q, r: new variables)
forceVarList :: [WeakTerm] -> WithEnv [Identifier]
forceVarList [] = return []
forceVarList ((_ :< WeakTermUpsilon x):es) = do
  xs <- forceVarList es
  return $ x : xs
forceVarList (_:es) = do
  x <- newNameWith "hole"
  xs <- forceVarList es
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
chain :: Q.MinQueue EnrichedConstraint -> [WithEnv a] -> WithEnv a
chain _ []     = throwError "cannot synthesize(chain)"
chain c (e:es) = e `catchError` const (chain c es)

lookupAny :: [Identifier] -> [(Identifier, a)] -> Maybe (Identifier, a)
lookupAny [] _ = Nothing
lookupAny (k:ks) sub =
  case lookup k sub of
    Just v  -> Just (k, v)
    Nothing -> lookupAny ks sub
