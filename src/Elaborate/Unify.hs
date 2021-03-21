module Elaborate.Unify
  ( unify,
  )
where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import Data.List (nubBy)
import Data.Log
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Simplify

unify :: WithEnv ()
unify =
  analyze >> synthesize

analyze :: WithEnv ()
analyze = do
  cs <- gets constraintEnv
  modify (\env -> env {constraintEnv = []})
  simplify cs

synthesize :: WithEnv ()
synthesize = do
  cs <- gets suspendedConstraintEnv
  case cs of
    [] ->
      return ()
    _
      | otherwise ->
        throwTypeErrors

throwTypeErrors :: WithEnv ()
throwTypeErrors = do
  q <- gets suspendedConstraintEnv
  let pcs = nubBy (\x y -> fst x == fst y) $ setupPosInfo q
  errorList <- constructErrors [] pcs
  throw $ Error errorList

setupPosInfo :: [SuspendedConstraint] -> [(PosInfo, Constraint)]
setupPosInfo constraintList =
  case constraintList of
    [] ->
      []
    (_, (expectedTerm, actualTerm)) : cs -> do
      let loc = getPosInfo $ metaOf actualTerm
      (loc, (actualTerm, expectedTerm)) : setupPosInfo cs

constructErrors :: [PosInfo] -> [(PosInfo, Constraint)] -> WithEnv [Log]
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
