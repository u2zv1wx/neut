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
      e' <- nonRecReduce e
      ans <- bindFormalArgs' args e'
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
     -> do
      args <- mapM toVar' preArgs
      synthesizeFlexRigid q ctx hole args e t
    Just (Enriched _ (Constraint ctx (ConstraintFlexRigid hole args e) t))
      -- Synthesize `hole @ arg-1 @ ... @ arg-n = e`, where arg-i is an arbitrary term.
     -> synthesizeFlexRigid q ctx hole args e t
    Just c -> throwError $ "cannot synthesize:\n" ++ Pr.ppShow c

-- See the section 3 of "Elaboration in Dependent Type Theory".
-- In short: Try some dependent alternatives, and if all of them fails, try to solve
-- the constraint assuming that, in `hole @ arg-1 @ ... @ arg-n = e`, the `hole`
-- doesn't use `arg-i`.
synthesizeFlexRigid ::
     Q.MinQueue EnrichedConstraint
  -> Context
  -> Identifier
  -> [Neut]
  -> Neut
  -> Neut
  -> WithEnv ()
synthesizeFlexRigid q ctx hole args e t = do
  let (x, eArgs) = toPiElimSeq e
  newHoleList <- mapM (const (newNameWith "hole")) args -- ?M_i
  newHoleVarList <- mapM toVar' newHoleList
  newArgList <- mapM (const $ newNameWith "arg") eArgs -- x_i
  newVarList <- mapM toVar' newArgList
  argList <- forM newHoleVarList $ \h -> appFold' h newVarList -- ?M_i @ x_1 @ ... @ x_n
  bodyList <- forM (x : args) $ \v -> appFold' v argList
  lamList <- forM bodyList $ \body -> bindFormalArgs' newArgList body
  let compList =
        flip map lamList $ \lam -> do
          left <- appFold' lam args
          meta <- newNameWith "meta"
          getQueue $
            analyze [(ctx, left, e, t), (ctx, meta :< NeutHole hole, lam, t)]
  meta <- newNameWith "meta"
  lam <- bindFormalArgs' newHoleList e
  let independent = getQueue $ analyze [(ctx, meta :< NeutHole hole, lam, t)]
  q' <- chain q $ compList ++ [independent]
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
