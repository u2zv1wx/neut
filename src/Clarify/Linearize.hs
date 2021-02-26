module Clarify.Linearize
  ( linearize,
  )
where

import Clarify.Utility
import Data.Comp
import Data.Env
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.Log

-- insert an appropriate header for a closed chain
linearize ::
  [(Ident, CompPlus)] -> -- [(x1, t1), ..., (xn, tn)]  (closed chain)
  CompPlus ->
  WithEnv CompPlus
linearize xts =
  linearize' IntMap.empty (reverse xts)

type NameMap = IntMap.IntMap [Ident]

linearize' ::
  NameMap ->
  [(Ident, CompPlus)] -> -- [(xn, tn), ..., (x1, t1)]  (reversed closed chain)
  CompPlus ->
  WithEnv CompPlus
linearize' nm binder e =
  case binder of
    [] ->
      return e
    (x, t) : xts -> do
      (nmE, e') <- distinguishComp [x] e
      let newNm = merge [nmE, nm]
      e'' <- withHeader newNm x t e'
      linearize' newNm xts e''

-- insert header for a variable
withHeader :: NameMap -> Ident -> CompPlus -> CompPlus -> WithEnv CompPlus
withHeader nm x t e =
  case IntMap.lookup (asInt x) nm of
    Nothing ->
      withHeaderAffine x t e
    Just [] ->
      raiseCritical' $ "impossible. x: " <> asText' x
    Just [z] ->
      withHeaderLinear z x e
    Just (z1 : z2 : zs) ->
      withHeaderRelevant x t z1 z2 zs e

-- withHeaderAffine x t e ~>
--   bind _ :=
--     bind exp := t^# in        --
--     exp @ (0, x) in           -- AffineApp
--   e
withHeaderAffine :: Ident -> CompPlus -> CompPlus -> WithEnv CompPlus
withHeaderAffine x t e@(m, _) = do
  hole <- newNameWith' "unit"
  discardUnusedVar <- toAffineApp m x t
  return (m, CompUpElim hole discardUnusedVar e)

-- withHeaderLinear z x e ~>
--   bind z := return x in
--   e
withHeaderLinear :: Ident -> Ident -> CompPlus -> WithEnv CompPlus
withHeaderLinear z x e@(m, _) =
  return (m, CompUpElim z (m, CompUpIntro (m, ValueUpsilon x)) e)

-- withHeaderRelevant x t [x1, ..., x{N}] e ~>
--   bind exp := t in
--   bind sigTmp1 := exp @ (0, x) in               --
--   let (x1, tmp1) := sigTmp1 in                  --
--   ...                                           -- withHeaderRelevant'
--   bind sigTmp{N-1} := exp @ (0, tmp{N-2}) in    --
--   let (x{N-1}, x{N}) := sigTmp{N-1} in          --
--   e                                             --
-- (assuming N >= 2)
withHeaderRelevant ::
  Ident ->
  CompPlus ->
  Ident ->
  Ident ->
  [Ident] ->
  CompPlus ->
  WithEnv CompPlus
withHeaderRelevant x t x1 x2 xs e@(m, _) = do
  (expVarName, expVar) <- newValueUpsilonWith m "exp"
  linearChain <- toLinearChain $ x : x1 : x2 : xs
  rel <- withHeaderRelevant' t expVar linearChain e
  return (m, CompUpElim expVarName t rel)

type LinearChain = [(Ident, (Ident, Ident))]

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

-- withHeaderRelevant' expVar [(x1, (x2, tmpA)), (tmpA, (x3, tmpB)), (tmpB, (x3, x4))] ~>
--   bind sigVar1 := expVar @ (1, x1) in
--   let (x2, tmpA) := sigVar1 in
--   bind sigVar2 := expVar @ (1, tmpA) in
--   let (x3, tmpB) := sigVar2 in
--   bind sigVar3 := expVar @ (1, tmpB) in
--   let (x3, x4) := sigVar3 in
--   e
withHeaderRelevant' :: CompPlus -> ValuePlus -> LinearChain -> CompPlus -> WithEnv CompPlus
withHeaderRelevant' t expVar ch cont@(m, _) =
  case ch of
    [] ->
      return cont
    (x, (x1, x2)) : chain -> do
      cont' <- withHeaderRelevant' t expVar chain cont
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
            (m, sigmaElim [x1, x2] sigVar cont')
        )

merge :: [NameMap] -> NameMap
merge =
  foldr (IntMap.unionWith (++)) IntMap.empty

distinguishValue :: [Ident] -> ValuePlus -> WithEnv (NameMap, ValuePlus)
distinguishValue zs term =
  case term of
    (ml, ValueUpsilon x) ->
      if x `notElem` zs
        then return (IntMap.empty, term)
        else do
          x' <- newNameWith x
          return (IntMap.singleton (asInt x) [x'], (ml, ValueUpsilon x'))
    (ml, ValueSigmaIntro mk ds) -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue zs) ds
      return (merge vss, (ml, ValueSigmaIntro mk ds'))
    (m, ValueStructIntro dks) -> do
      let (ds, ks) = unzip dks
      (vss, ds') <- unzip <$> mapM (distinguishValue zs) ds
      return (merge vss, (m, ValueStructIntro $ zip ds' ks))
    _ ->
      return (IntMap.empty, term)

distinguishComp :: [Ident] -> CompPlus -> WithEnv (NameMap, CompPlus)
distinguishComp zs term =
  case term of
    (ml, CompPrimitive theta) -> do
      (vs, theta') <- distinguishPrimitive zs theta
      return (vs, (ml, CompPrimitive theta'))
    (ml, CompPiElimDownElim d ds) -> do
      (vs, d') <- distinguishValue zs d
      (vss, ds') <- unzip <$> mapM (distinguishValue zs) ds
      return (merge $ vs : vss, (ml, CompPiElimDownElim d' ds'))
    (ml, CompSigmaElim mk xs d e) -> do
      (vs1, d') <- distinguishValue zs d
      let zs' = filter (`notElem` xs) zs
      (vs2, e') <- distinguishComp zs' e
      return (merge [vs1, vs2], (ml, CompSigmaElim mk xs d' e'))
    (ml, CompUpIntro d) -> do
      (vs, d') <- distinguishValue zs d
      return (vs, (ml, CompUpIntro d'))
    (ml, CompUpElim x e1 e2) -> do
      (vs1, e1') <- distinguishComp zs e1
      if x `elem` zs
        then return (vs1, (ml, CompUpElim x e1' e2))
        else do
          (vs2, e2') <- distinguishComp zs e2
          return (merge [vs1, vs2], (ml, CompUpElim x e1' e2'))
    (ml, CompEnumElim d branchList) -> do
      (vs, d') <- distinguishValue zs d
      let (cs, es) = unzip branchList
      (vss, es') <- unzip <$> mapM (distinguishComp zs) es
      return (merge $ vs : vss, (ml, CompEnumElim d' (zip cs es')))
    (ml, CompStructElim xts d e) -> do
      (vs1, d') <- distinguishValue zs d
      let zs' = filter (`notElem` map fst xts) zs
      (vs2, e') <- distinguishComp zs' e
      return (merge [vs1, vs2], (ml, CompStructElim xts d' e'))

distinguishPrimitive :: [Ident] -> Primitive -> WithEnv (NameMap, Primitive)
distinguishPrimitive zs term =
  case term of
    PrimitiveUnaryOp op d -> do
      (vs, d') <- distinguishValue zs d
      return (vs, PrimitiveUnaryOp op d')
    PrimitiveBinaryOp op d1 d2 -> do
      (vs1, d1') <- distinguishValue zs d1
      (vs2, d2') <- distinguishValue zs d2
      return (merge [vs1, vs2], PrimitiveBinaryOp op d1' d2')
    PrimitiveArrayAccess lowType d1 d2 -> do
      (vs1, d1') <- distinguishValue zs d1
      (vs2, d2') <- distinguishValue zs d2
      return (merge [vs1, vs2], PrimitiveArrayAccess lowType d1' d2')
    PrimitiveSyscall num ds -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue zs) ds
      return (merge vss, PrimitiveSyscall num ds')
