module Elaborate.Synthesize
  ( synthesize
  ) where

import Control.Monad
import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Trans.Except

import Control.Comonad.Cofree

import qualified Text.Show.Pretty as Pr

import Data
import Elaborate.Analyze
import Reduce
import Util

import Data.List

import Data.Maybe

import qualified Data.PQueue.Min as Q

-- Given a queue of constraints (easier ones comes earlier), try to synthesize
-- all of them using heuristics.
synthesize :: Q.MinQueue EnrichedConstraint -> WithEnv ()
synthesize q =
  case Q.getMin q of
    Nothing -> return ()
    Just (Enriched _ (Constraint _ (ConstraintPattern x args e) _))
      -- Synthesize `?M @ arg-1 @ ... @ arg-n == e`, where each arg-i is a variable,
      -- and arg-i == arg-j iff i == j. This kind of constraint is known to be able
      -- to be solved by:
      --   ?M == lam arg-1, ..., arg-n. e
      -- This kind of constraint is called a "pattern".
     -> do
      ans <- bindFormalArgs' args e
      modify (\e -> e {substitution = compose [(x, ans)] (substitution e)})
      substQueue (Q.deleteMin q) >>= synthesize
    Just (Enriched _ (Constraint ctx (ConstraintBeta x body) t))
      -- Synthesize `var == body` (note that `var` is not a meta-variable).
      -- In this case, we insert (var -> body) in the substitution environment
      -- so that we can extract this definition when needed.
      -- If there already exists a definition of same name `var`, we add a
      -- constraint that the existing body and the new body is the same, or more
      -- precisely, beta-convertible.
     -> do
      me <- insDef x body
      case me of
        Nothing -> synthesize $ Q.deleteMin q
        Just body' -> do
          cs <- simp [(ctx, body, body', t)]
          let q' = Q.fromList $ map (\c -> Enriched c $ categorize c) cs
          synthesize $ Q.deleteMin q `Q.union` q'
    Just (Enriched _ (Constraint ctx (ConstraintDelta x args1 args2) t))
      -- Synthesize `x @ arg-11 @ ... @ arg-1n == x @ arg-21 @ ... @ arg-2n`.
      -- We try two alternatives:
      --   (1) assume that x is opaque and attempt to resolve this by args1 === args2.
      --   (2) unfold the definition of x and resolve (unfold x) @ args1 == (unfold x) @ args2.
      -- In (2), we use the definition that are inserted by ConstraintBeta.
     -> do
      let plan1 = do
            cs <- simp $ map (\(e1, e2) -> (ctx, e1, e2, t)) $ zip args1 args2
            getQueue $ analyze cs
      sub <- gets substitution
      planList <-
        case lookup x sub of
          Nothing -> return [plan1]
          Just body -> do
            e1' <- appFold' body args1 >>= reduce
            e2' <- appFold' body args2 >>= reduce
            cs <- simp [(ctx, e1', e2', t)]
            let plan2 = getQueue $ analyze cs
            return [plan1, plan2]
      q <- gets constraintQueue
      chain q planList >>= continue q
    Just (Enriched _ (Constraint ctx (ConstraintQuasiPattern hole preArgs e) t))
      -- Synthesize `hole @ arg-1 @ ... @ arg-n = e`, where arg-i is a variable.
      -- In this case, we do the same as in Flex-Rigid case.
      -- The distinction here is required just to ensure that we deal with
      -- constraints from easier ones.
     -> synthesizeQuasiPattern q ctx hole preArgs e t
    Just (Enriched _ (Constraint ctx (ConstraintFlexRigid hole args e) t))
      -- Synthesize `hole @ arg-1 @ ... @ arg-n = e`, where arg-i is an arbitrary term.
     -> synthesizeFlexRigid q ctx hole args e t
    Just c -> throwError $ "cannot synthesize:\n" ++ Pr.ppShow c

-- Suppose that this function received a quasi-pattern ?M @ x @ x @ y @ z == e, for example.
-- What this function do is to try two alternatives in this case:
--   (1) ?M == lam x. lam _. lam y. lam z. e
--   (2) ?M == lam _. lam x. lam y. lam z. e
-- where the `_` is a new variable. In other words, this function tries all the alternatives
-- that are obtained by choosing one `x` from the list [x, x, y, z], replacing all the
-- other occurrences of `x` with new variables.
synthesizeQuasiPattern ::
     Q.MinQueue EnrichedConstraint
  -> PreContext
  -> Identifier
  -> [Identifier]
  -> Neut
  -> Neut
  -> WithEnv ()
synthesizeQuasiPattern q ctx hole preArgs e t = do
  argsList <- toAltList preArgs
  meta <- newNameWith "meta"
  lamList <- mapM (`bindFormalArgs'` e) argsList
  let planList =
        flip map lamList $ \lam ->
          getQueue $ analyze [(ctx, meta :< NeutHole hole, lam, t)]
  q' <- chain q planList
  continue q q'

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

-- This function just tries to resolve the constraint by assuming that the meta-variable
-- discards all the arguments. For example, given a constraint `?M @ e1 @ e2 = e`, this
-- function tries to resolve this by `?M = lam _. lam _. e`, discarding the arguments
-- `e1` and `e2`.
synthesizeFlexRigid ::
     Q.MinQueue EnrichedConstraint
  -> PreContext
  -> Identifier
  -> [Neut]
  -> Neut
  -> Neut
  -> WithEnv ()
synthesizeFlexRigid q ctx hole args e t = do
  newHoleList <- mapM (const (newNameWith "hole")) args -- ?M_i
  meta <- newNameWith "meta"
  lam <- bindFormalArgs' newHoleList e
  let independent = getQueue $ analyze [(ctx, meta :< NeutHole hole, lam, t)]
  q' <- chain q [independent]
  continue q q'

getQueue :: WithEnv a -> WithEnv (Q.MinQueue EnrichedConstraint)
getQueue command = do
  modify (\e -> e {constraintQueue = Q.empty})
  command
  gets constraintQueue

continue ::
     Q.MinQueue EnrichedConstraint
  -> Q.MinQueue EnrichedConstraint
  -> WithEnv ()
continue currentQueue newQueue = do
  let q = Q.deleteMin currentQueue `Q.union` newQueue
  substQueue q >>= synthesize

-- Try the list of alternatives.
chain :: Q.MinQueue EnrichedConstraint -> [WithEnv a] -> WithEnv a
chain c [] = throwError $ "cannot synthesize:\n" ++ Pr.ppShow c
chain c (e:es) = e `catchError` const (chain c es)

substQueue ::
     Q.MinQueue EnrichedConstraint -> WithEnv (Q.MinQueue EnrichedConstraint)
substQueue q = updateQueue q >> gets constraintQueue
