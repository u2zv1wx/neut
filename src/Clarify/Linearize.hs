module Clarify.Linearize
  ( linearize,
  )
where

import Clarify.Utility
import Data.Basic
import Data.Comp
import Data.Env

type LinearChain = [(Ident, (Ident, Ident))]

linearize ::
  [(Ident, CompPlus)] -> -- [(x1, t1), ..., (xn, tn)]  (closed chain)
  CompPlus -> -- a term that can contain non-linear occurrences of xi
  WithEnv CompPlus -- a term in which all the variables in the closed chain occur linearly
linearize binder e =
  case binder of
    [] ->
      return e
    (x, t) : xts -> do
      e' <- linearize xts e
      (newNameList, e'') <- distinguishComp x e'
      case newNameList of
        [] ->
          insertHeaderForAffine x t e''
        [z] ->
          insertHeaderForLinear x z e''
        _ -> do
          insertHeaderForRelevant (x : newNameList) t e''

-- insertHeaderForAffine x t e ~>
--   bind _ :=
--     bind exp := t^# in        --
--     exp @ (0, x) in           -- AffineApp
--   e
insertHeaderForAffine :: Ident -> CompPlus -> CompPlus -> WithEnv CompPlus
insertHeaderForAffine x t e@(m, _) = do
  hole <- newNameWith' "unit"
  discardUnusedVar <- toAffineApp m x t
  return (m, CompUpElim hole discardUnusedVar e)

-- insertHeaderForLinear z x e ~>
--   bind z := return x in
--   e
insertHeaderForLinear :: Ident -> Ident -> CompPlus -> WithEnv CompPlus
insertHeaderForLinear x z e@(m, _) =
  return (m, CompUpElim z (m, CompUpIntro (m, ValueUpsilon x)) e)

-- insertHeaderForRelevant [x, x1, ..., x{N}] t e ~>
--   bind exp := t in
--   bind sigTmp1 := exp @ (1, x) in               --
--   let (x1, tmp1) := sigTmp1 in                  --
--   ...                                           -- insertHeaderForRelevant'
--   bind sigTmp{N-1} := exp @ (1, tmp{N-2}) in    --
--   let (x{N-1}, x{N}) := sigTmp{N-1} in          --
--   e                                             --
-- (assuming N >= 2)
insertHeaderForRelevant ::
  [Ident] ->
  CompPlus ->
  CompPlus ->
  WithEnv CompPlus
insertHeaderForRelevant xs t e@(m, _) = do
  (expVarName, expVar) <- newValueUpsilonWith m "exp"
  linearChain <- toLinearChain xs
  rel <- insertHeaderForRelevant' t expVar linearChain e
  return (m, CompUpElim expVarName t rel)

--    toLinearChain [x0, x1, x2, ..., x{N-1}] (N >= 3)
-- ~> [(x0, (x1, tmp1)), (tmp1, (x2, tmp2)), ..., (tmp{N-3}, (x{N-2}, x{N-1}))]
--
-- example behavior (length xs = 5):
--   xs = [x1, x2, x3, x4, x5]
--   valueSeq = [x2, x3, x4]
--   tmpSeq = [tmpA, tmpB]
--   tmpSeq' = [x1, tmpA, tmpB, x5]
--   pairSeq = [(x2, tmpA), (x3, tmpB), (x4, x5)]
--   result = [(x1, (x2, tmpA)), (tmpA, (x3, tmpB)), (tmpB, (x4, x5))]
--
-- example behavior (length xs = 3):
--   xs = [x1, x2, x3]
--   valueSeq = [x2]
--   tmpSeq = []
--   tmpSeq' = [x1, x3]
--   pairSeq = [(x2, x3)]
--   result = [(x1, (x2, x3))]
toLinearChain :: [Ident] -> WithEnv LinearChain
toLinearChain xs = do
  let valueSeq = init $ tail xs
  tmpSeq <- mapM (const $ newNameWith' "chain") $ replicate (length xs - 3) ()
  let tmpSeq' = [head xs] ++ tmpSeq ++ [last xs]
  let pairSeq = zip valueSeq (tail tmpSeq')
  return $ zip (init tmpSeq') pairSeq

-- insertHeaderForRelevant' expVar [(x1, (x2, tmpA)), (tmpA, (x3, tmpB)), (tmpB, (x3, x4))] ~>
--   bind sigVar1 := expVar @ (1, x1) in
--   let (x2, tmpA) := sigVar1 in
--   bind sigVar2 := expVar @ (1, tmpA) in
--   let (x3, tmpB) := sigVar2 in
--   bind sigVar3 := expVar @ (1, tmpB) in
--   let (x3, x4) := sigVar3 in
--   e
insertHeaderForRelevant' :: CompPlus -> ValuePlus -> LinearChain -> CompPlus -> WithEnv CompPlus
insertHeaderForRelevant' t expVar ch cont@(m, _) =
  case ch of
    [] ->
      return cont
    (x, (x1, x2)) : chain -> do
      cont' <- insertHeaderForRelevant' t expVar chain cont
      (sigVarName, sigVar) <- newValueUpsilonWith m "sig"
      return
        ( m,
          CompUpElim
            sigVarName
            ( m,
              CompPiElimDownElim
                expVar
                [(m, ValueEnumIntro boolTrue), (m, ValueUpsilon x)]
            )
            (m, CompSigmaElim [x1, x2] sigVar cont')
        )

distinguishValue :: Ident -> ValuePlus -> WithEnv ([Ident], ValuePlus)
distinguishValue z term =
  case term of
    (m, ValueUpsilon x) ->
      if x /= z
        then return ([], term)
        else do
          x' <- newNameWith x
          return ([x'], (m, ValueUpsilon x'))
    (m, ValueSigmaIntro ds) -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat vss, (m, ValueSigmaIntro ds'))
    _ ->
      return ([], term)

distinguishComp :: Ident -> CompPlus -> WithEnv ([Ident], CompPlus)
distinguishComp z term =
  case term of
    (m, CompPrimitive theta) -> do
      (vs, theta') <- distinguishPrimitive z theta
      return (vs, (m, CompPrimitive theta'))
    (m, CompPiElimDownElim d ds) -> do
      (vs, d') <- distinguishValue z d
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat $ vs : vss, (m, CompPiElimDownElim d' ds'))
    (m, CompSigmaElim xs d e) -> do
      (vs1, d') <- distinguishValue z d
      (vs2, e') <- distinguishComp z e
      return (concat [vs1, vs2], (m, CompSigmaElim xs d' e'))
    (m, CompUpIntro d) -> do
      (vs, d') <- distinguishValue z d
      return (vs, (m, CompUpIntro d'))
    (m, CompUpElim x e1 e2) -> do
      (vs1, e1') <- distinguishComp z e1
      (vs2, e2') <- distinguishComp z e2
      return (concat [vs1, vs2], (m, CompUpElim x e1' e2'))
    (m, CompEnumElim d branchList) -> do
      (vs, d') <- distinguishValue z d
      let (cs, es) = unzip branchList
      (vss, es') <- unzip <$> mapM (distinguishComp z) es
      return (concat $ vs : vss, (m, CompEnumElim d' (zip cs es')))

distinguishPrimitive :: Ident -> Primitive -> WithEnv ([Ident], Primitive)
distinguishPrimitive z term =
  case term of
    PrimitivePrimOp op ds -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat vss, PrimitivePrimOp op ds')
    PrimitiveDerangement k ds -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat vss, PrimitiveDerangement k ds')
