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
    Just (Enriched (e1, e2) (ConstraintQuasiPattern _ m _ _))
      | Just e <- lookup m sub -> resolveStuck q e1 e2 m e
    Just (Enriched (e1, e2) (ConstraintFlexRigid _ m _ _))
      | Just e <- lookup m sub -> resolveStuck q e1 e2 m e
    Just (Enriched (e1, e2) (ConstraintOther ms))
      | Just (m, e) <- lookupAny ms sub -> resolveStuck q e1 e2 m e
    Just (Enriched _ (ConstraintQuasiPattern s m preArgs e))
      -- Synthesize `hole @ arg-1 @ ... @ arg-n = e`, where arg-i is a variable.
      -- Suppose that we received a quasi-pattern ?M @ x @ x @ y @ z == e.
      -- What this function do is to try two alternatives in this case:
      --   (1) ?M == lam x. lam _. lam y. lam z. e
      --   (2) ?M == lam _. lam x. lam y. lam z. e
      -- where `_` are new variables. In other words, this function tries
      -- all the alternatives that are obtained by choosing one `x` from the
      -- list [x, x, y, z], replacing all the other occurrences of `x` with new variables.
     -> do
      argsList <- toAltList preArgs
      lamList <- mapM (\xs -> bindFormalArgs s xs e) argsList
      chain q $
        flip map lamList $ \lam -> do
          modify (\env -> env {substEnv = compose [(m, lam)] (substEnv env)})
          synthesize $ Q.deleteMin q
    Just (Enriched _ (ConstraintFlexRigid s m args e))
      -- Synthesize `hole @ arg-1 @ ... @ arg-n = e`, where arg-i is an arbitrary term.
      -- We try to resolve the constraint by assuming that the meta-variable
      -- discards all the arguments. For example, given a constraint `?M @ e1 @ e2 = e`, this
      -- function tries to resolve this by `?M = lam _. lam _. e`, discarding the arguments
      -- `e1` and `e2`.
     -> do
      newHoleList <- mapM (const (newNameWith "hole")) args -- ?M_i
      lam <- bindFormalArgs s newHoleList e
      modify (\env -> env {substEnv = compose [(m, lam)] (substEnv env)})
      synthesize $ Q.deleteMin q
    Just _ -> throwError "cannot synthesize(synth)"

resolveStuck ::
     Q.MinQueue EnrichedConstraint
  -> WeakTerm
  -> WeakTerm
  -> Identifier
  -> WeakTerm
  -> WithEnv ()
resolveStuck q e1 e2 hole e = do
  let e1' = substWeakTerm [(hole, e)] e1
  let e2' = substWeakTerm [(hole, e)] e2
  cs <- analyze [(e1', e2')]
  synthesize $ Q.deleteMin q `Q.union` Q.fromList cs

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
