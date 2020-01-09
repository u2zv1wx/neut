module Elaborate.Synthesize
  ( synthesize
  ) where

import Control.Monad.Except
import Control.Monad.State

import qualified Data.PQueue.Min as Q
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Constraint
import Data.Env
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer (insWeakTypeEnv, metaTerminal, typeOf)
import Reduce.WeakTerm

-- Given a queue of constraints (easier ones comes earlier), try to synthesize
-- all of them using heuristics.
synthesize :: ConstraintQueue -> WithEnv ()
synthesize q = do
  sub <- gets substEnv
  case Q.getMin q of
    Nothing -> return ()
    Just (Enriched (e1, e2) ms _ _)
      | Just (m, (_, e)) <- lookupAny ms sub -> resolveStuck q e1 e2 m e
    Just (Enriched _ _ fmvs (ConstraintPattern m ess e)) -> do
      resolvePiElim q m fmvs ess e
    Just (Enriched _ _ fmvs (ConstraintQuasiPattern m ess e)) -> do
      resolvePiElim q m fmvs ess e
    Just (Enriched _ _ fmvs (ConstraintFlexRigid m ess e)) -> do
      resolvePiElim q m fmvs ess e
    Just (Enriched (e1, e2) _ _ _) ->
      throwError $ "cannot simplify:\n" ++ Pr.ppShow (e1, e2)

resolveStuck ::
     ConstraintQueue
  -> WeakTermPlus
  -> WeakTermPlus
  -> Hole
  -> WeakTermPlus
  -> WithEnv ()
resolveStuck q e1 e2 h e = do
  let fmvs = holeWeakTermPlus e
  let e1' = substWeakTermPlus [(h, e)] e1
  let e2' = substWeakTermPlus [(h, e)] e2
  q' <- analyze [(e1', e2')] >>= assert "resolveStuck" (h `notElem` fmvs)
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
     ConstraintQueue
  -> Hole
  -> [Hole]
  -> [[WeakTermPlus]]
  -> WeakTermPlus
  -> WithEnv ()
resolvePiElim q m fmvs ess e = do
  lengthInfo <- assert "piElim" (m `notElem` fmvs) $ map length ess
  let es = concat ess
  xss <- toVarList es >>= toAltList
  let xsss = map (takeByCount lengthInfo) xss
  let lamList = map (bindFormalArgs e) xsss
  chain q $ map (\lam -> resolveHole q m fmvs lam) lamList

resolveHole :: ConstraintQueue -> Hole -> [Hole] -> WeakTermPlus -> WithEnv ()
resolveHole q m fmvs e = do
  senv <- gets substEnv
  e' <- reduceWeakTermPlus $ snd $ substIfNecessary senv (fmvs, e)
  let fmvs' = holeWeakTermPlus e'
  modify (\env -> env {substEnv = compose [(m, (fmvs', e'))] senv})
  let (q1, q2) =
        Q.partition (\(Enriched _ ms _ _) -> m `elem` ms) $ Q.deleteMin q
  let q1' = Q.mapU asAnalyzable q1
  synthesize $ q1' `Q.union` q2

asAnalyzable :: EnrichedConstraint -> EnrichedConstraint
asAnalyzable (Enriched cs ms fmvs _) = Enriched cs ms fmvs ConstraintAnalyzable

-- [e, x, y, y, e2, e3, z] ~> [p, x, y, y, q, r, z]  (p, q, r: new variables)
toVarList :: [WeakTermPlus] -> WithEnv [(Identifier, WeakTermPlus)]
toVarList [] = return []
toVarList ((_, WeakTermUpsilon x):es) = do
  xts <- toVarList es
  let t = (metaTerminal, WeakTermUpsilon "DONT_CARE")
  return $ (x, t) : xts
toVarList (_:es) = do
  xts <- toVarList es
  x <- newNameWith "hole"
  let t = (metaTerminal, WeakTermUpsilon "DONT_CARE")
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
chain _ [e] = e
chain c (e:es) = catchError e $ (const $ chain c es)

lookupAny :: [Hole] -> [(Identifier, a)] -> Maybe (Hole, a)
lookupAny [] _ = Nothing
lookupAny (h:ks) sub = do
  case lookup h sub of
    Just v -> Just (h, v)
    _ -> lookupAny ks sub

bindFormalArgs :: WeakTermPlus -> [[IdentifierPlus]] -> WeakTermPlus
bindFormalArgs e [] = e
bindFormalArgs e (xts:xtss) = do
  let e' = bindFormalArgs e xtss
  let tPi = (metaTerminal, WeakTermPi xts (typeOf e'))
  (PreMetaNonTerminal tPi emptyMeta, WeakTermPiIntro xts e')

-- takeByCount [1, 3, 2] [a, b, c, d, e, f, g, h] ~> [[a], [b, c, d], [e, f]]
takeByCount :: [Int] -> [a] -> [[a]]
takeByCount [] _ = []
takeByCount (i:is) xs = do
  let ys = take i xs
  let yss = takeByCount is (drop i xs)
  ys : yss
