{-# LANGUAGE OverloadedStrings #-}

module Clarify.Linearize
  ( linearize
  ) where

import qualified Data.HashMap.Strict as Map

import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env

-- insert header for a closed chain
linearize ::
     [(Identifier, CodePlus)] -- [(x1, t1), ..., (xn, tn)]  (closed chain)
  -> CodePlus
  -> WithEnv CodePlus
linearize xts e = do
  (nm, e') <- distinguishCode (map fst xts) e
  linearize' nm (reverse xts) e'

type NameMap = Map.HashMap Identifier [Identifier]

linearize' ::
     NameMap
  -> [(Identifier, CodePlus)] -- [(xn, tn), ..., (x1, t1)]  (reversed closed chain)
  -> CodePlus
  -> WithEnv CodePlus
linearize' _ [] e = return e -- ここでnamemapを返すようにする？
linearize' nm ((x, t):xts) e = do
  (nmT, t') <- distinguishCode (map fst xts) t
  let newNm = merge [nmT, nm]
  e' <- withHeader newNm x t' e
  linearize' newNm xts e'

-- insert header for a variable
withHeader :: NameMap -> Identifier -> CodePlus -> CodePlus -> WithEnv CodePlus
withHeader nm x t e =
  case Map.lookup x nm of
    Nothing -> withHeaderAffine x t e
    Just [] -> error $ "impossible. x: " ++ show x
    Just [z] -> withHeaderLinear z x e
    Just (z1:z2:zs) -> withHeaderRelevant x t z1 z2 zs e

-- withHeaderAffine x t e ~>
--   bind _ :=
--     bind exp := t^# in        --
--     let (aff, rel) := exp in  -- AffineApp
--     aff @ x in                --
--   e
-- 変数xに型t由来のaffineを適用して破棄する。
withHeaderAffine :: Identifier -> CodePlus -> CodePlus -> WithEnv CodePlus
withHeaderAffine x t e = do
  hole <- newNameWith "unit"
  discardUnusedVar <- toAffineApp emptyMeta x t
  return (emptyMeta, CodeUpElim hole discardUnusedVar e)

-- withHeaderLinear z x e ~>
--   bind z := return x in
--   e
-- renameするだけ。
withHeaderLinear :: Identifier -> Identifier -> CodePlus -> WithEnv CodePlus
withHeaderLinear z x e = do
  let m = emptyMeta
  return (m, CodeUpElim z (m, CodeUpIntro (m, DataUpsilon x)) e)

-- withHeaderRelevant x t [x1, ..., x{N}] e ~>
--   bind exp := t in
--   let (aff, rel) := exp in
--   bind sigTmp1 := rel @ x in                    --
--   let (x1, tmp1) := sigTmp1 in                  --
--   ...                                           -- withHeaderRelevant'
--   bind sigTmp{N-1} := rel @ tmp{N-2} in         --
--   let (x{N-1}, x{N}) := sigTmp{N-1} in          --
--   e                                             --
-- (assuming N >= 2)
withHeaderRelevant ::
     Identifier
  -> CodePlus
  -> Identifier
  -> Identifier
  -> [Identifier]
  -> CodePlus
  -> WithEnv CodePlus
withHeaderRelevant x t x1 x2 xs e = do
  (expVarName, expVar) <- newDataUpsilonWith "exp"
  (affVarName, _) <- newDataUpsilonWith "aff"
  (relVarName, relVar) <- newDataUpsilonWith "rel"
  linearChain <- toLinearChain $ x : x1 : x2 : xs
  let ml = fst e
  rel <- withHeaderRelevant' t relVar linearChain e
  retImmType <- returnCartesianImmediate
  return
    ( ml
    , CodeUpElim
        expVarName
        t
        ( ml
        , CodeSigmaElim
            arrVoidPtr
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            rel))

type LinearChain = [(Identifier, (Identifier, Identifier))]

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
toLinearChain :: [Identifier] -> WithEnv LinearChain
toLinearChain xs = do
  let valueSeq = init $ tail xs
  tmpSeq <-
    mapM (const $ newNameWith "linear-chain") $ replicate (length xs - 3) ()
  let tmpSeq' = [head xs] ++ tmpSeq ++ [last xs]
  let pairSeq = zip valueSeq (tail tmpSeq')
  return $ zip (init tmpSeq') pairSeq

-- withHeaderRelevant' relVar [(x1, (x2, tmpA)), (tmpA, (x3, tmpB)), (tmpB, (x3, x4))] ~>
--   bind sigVar1 := relVar @ x1 in
--   let (x2, tmpA) := sigVar1 in
--   bind sigVar2 := relVar @ tmpA in
--   let (x3, tmpB) := sigVar2 in
--   bind sigVar3 := relVar @ tmpB in
--   let (x3, x4) := sigVar3 in
--   e
withHeaderRelevant' ::
     CodePlus -> DataPlus -> LinearChain -> CodePlus -> WithEnv CodePlus
withHeaderRelevant' _ _ [] cont = return cont
withHeaderRelevant' t relVar ((x, (x1, x2)):chain) cont = do
  let m = fst cont
  cont' <- withHeaderRelevant' t relVar chain cont
  (sigVarName, sigVar) <- newDataUpsilonWith "sig"
  let varX = toDataUpsilon (x, emptyMeta)
  return $
    ( m
    , CodeUpElim
        sigVarName
        (m, CodePiElimDownElim relVar [varX])
        (m, CodeSigmaElim arrVoidPtr [(x1, t), (x2, t)] sigVar cont'))

merge :: [NameMap] -> NameMap
merge [] = Map.empty
merge (m:ms) = Map.unionWith (++) m $ merge ms

distinguishData :: [Identifier] -> DataPlus -> WithEnv (NameMap, DataPlus)
distinguishData zs d@(ml, DataUpsilon x) =
  if x `notElem` zs
    then return (Map.empty, d)
    else do
      x' <- newNameWith x
      return (Map.singleton x [x'], (ml, DataUpsilon x'))
distinguishData zs (ml, DataSigmaIntro mk ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge vss, (ml, DataSigmaIntro mk ds'))
distinguishData zs (m, DataStructIntro dks) = do
  let (ds, ks) = unzip dks
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge vss, (m, DataStructIntro $ zip ds' ks))
distinguishData _ d = return (Map.empty, d)

distinguishCode :: [Identifier] -> CodePlus -> WithEnv (NameMap, CodePlus)
distinguishCode zs (ml, CodeTheta theta) = do
  (vs, theta') <- distinguishTheta zs theta
  return (vs, (ml, CodeTheta theta'))
distinguishCode zs (ml, CodePiElimDownElim d ds) = do
  (vs, d') <- distinguishData zs d
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge $ vs : vss, (ml, CodePiElimDownElim d' ds'))
distinguishCode zs (ml, CodeSigmaElim mk xts d e) = do
  (vs1, d') <- distinguishData zs d
  let zs' = filter (`notElem` map fst xts) zs
  (vs2, e') <- distinguishCode zs' e
  return (merge [vs1, vs2], (ml, CodeSigmaElim mk xts d' e'))
distinguishCode zs (ml, CodeUpIntro d) = do
  (vs, d') <- distinguishData zs d
  return (vs, (ml, CodeUpIntro d'))
distinguishCode zs (ml, CodeUpElim x e1 e2) = do
  (vs1, e1') <- distinguishCode zs e1
  if x `elem` zs
    then return (vs1, (ml, CodeUpElim x e1' e2))
    else do
      (vs2, e2') <- distinguishCode zs e2
      return (merge [vs1, vs2], (ml, CodeUpElim x e1' e2'))
distinguishCode zs (ml, CodeEnumElim varInfo d branchList) = do
  (vs, d') <- distinguishData zs d
  let (from, to) = unzip varInfo
  (vss, to') <- unzip <$> mapM (distinguishData zs) to
  let varInfo' = zip from to'
  return (merge (vs : vss), (ml, CodeEnumElim varInfo' d' branchList))
distinguishCode zs (ml, CodeStructElim xts d e) = do
  (vs1, d') <- distinguishData zs d
  let zs' = filter (`notElem` map fst xts) zs
  (vs2, e') <- distinguishCode zs' e
  return (merge [vs1, vs2], (ml, CodeStructElim xts d' e'))

distinguishTheta :: [Identifier] -> Theta -> WithEnv (NameMap, Theta)
distinguishTheta zs (ThetaUnaryOp op lowType d) = do
  (vs, d') <- distinguishData zs d
  return (vs, ThetaUnaryOp op lowType d')
distinguishTheta zs (ThetaBinaryOp op lowType d1 d2) = do
  (vs1, d1') <- distinguishData zs d1
  (vs2, d2') <- distinguishData zs d2
  return (merge [vs1, vs2], ThetaBinaryOp op lowType d1' d2')
distinguishTheta zs (ThetaArrayAccess lowType d1 d2) = do
  (vs1, d1') <- distinguishData zs d1
  (vs2, d2') <- distinguishData zs d2
  return (merge [vs1, vs2], ThetaArrayAccess lowType d1' d2')
distinguishTheta zs (ThetaSysCall num ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge vss, ThetaSysCall num ds')
