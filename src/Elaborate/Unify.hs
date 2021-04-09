module Elaborate.Unify
  ( unify,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import Data.Log
import qualified Data.PQueue.Min as Q
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Simplify
import Reduce.WeakTerm

unify :: WithEnv ()
unify =
  analyze >> synthesize

analyze :: WithEnv ()
analyze = do
  cs <- gets constraintEnv
  modify (\env -> env {constraintEnv = []})
  simplify $ zip cs cs

synthesize :: WithEnv ()
synthesize = do
  cs <- gets suspendedConstraintEnv
  case Q.minView cs of
    Nothing ->
      return ()
    Just ((SuspendedConstraint (_, ConstraintKindDelta, (c, orig))), cs') -> do
      modify (\env -> env {suspendedConstraintEnv = cs'})
      simplify [(c, orig)]
      synthesize
    Just ((SuspendedConstraint (_, ConstraintKindOther, _)), _) ->
      throwTypeErrors

throwTypeErrors :: WithEnv a
throwTypeErrors = do
  q <- gets suspendedConstraintEnv
  sub <- gets substEnv
  errorList <- forM (Q.toList q) $ \(SuspendedConstraint (_, _, (_, (expected, actual)))) -> do
    expected' <- substWeakTermPlus sub expected >>= reduceWeakTermPlus
    actual' <- substWeakTermPlus sub actual >>= reduceWeakTermPlus
    return $ logError (getPosInfo (fst actual)) $ constructErrorMsg actual' expected'
  throw $ Error errorList

constructErrorMsg :: WeakTermPlus -> WeakTermPlus -> T.Text
constructErrorMsg e1 e2 =
  "couldn't verify the definitional equality of the following two terms:\n- "
    <> toText e1
    <> "\n- "
    <> toText e2
