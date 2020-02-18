{-# LANGUAGE OverloadedStrings #-}

module Clarify.Linearize
  ( linearize
  ) where

import qualified Data.HashMap.Strict as Map

import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env

-- linearizeの第1引数はeのなかでlinearに使用されるべき自由変数のリスト。closed chainでなければならないことに注意。
-- [x1, ..., xn] = map fst xtsとする。
-- {xtsはclosed chain} linearize {resultにおいて、x1, ..., xnはすべてlinearに出現する}
-- 「出現するならばlinearである」ってしたほうがいいのか？
linearize :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
linearize xts e = linearize' xts e

-- e' <- linearize xts eのとき、e'は、eとbeta-equivalentであり、かつ、xtsに含まれる変数の使用がlinearであるようなterm.
linearize' :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
linearize' xts (m, CodeSigmaElim ArrayKindVoidPtr yts d e) = do
  let xts' = filter (\(x, _) -> x `elem` varCode e) xts
  e' <- linearize (xts' ++ yts) e
  withHeader xts (m, CodeSigmaElim ArrayKindVoidPtr yts d e')
linearize' xts (m, CodeSigmaElim k ys d e) = do
  let xts' = filter (\(x, _) -> x `elem` varCode e) xts
  e' <- linearize xts' e
  withHeader xts (m, CodeSigmaElim k ys d e')
linearize' xts (m, CodeUpElim z e1 e2) = do
  let xts2' = filter (\(x, _) -> x `elem` varCode e2) xts
  e2' <- linearize xts2' e2
  let xts1' = filter (\(x, _) -> x `elem` varCode e1) xts
  e1' <- linearize xts1' e1
  withHeader xts (m, CodeUpElim z e1' e2')
linearize' xts (m, CodeEnumElim d les) = do
  let (ls, es) = unzip les
  let xts' = filter (\(x, _) -> x `elem` concatMap varCode es) xts
  es' <- mapM (linearize xts') es
  withHeader xts (m, CodeEnumElim d $ zip ls es')
linearize' xts (m, CodeStructElim yks d e) = do
  let xts' = filter (\(x, _) -> x `elem` varCode e) xts
  e' <- linearize xts' e
  withHeader xts (m, CodeStructElim yks d e')
linearize' xts e = withHeader xts e -- e doesn't contain any CodePlus

-- eのなかでxtsがpractically linearになるよう適切にheaderを挿入する。
-- withHeaderの引数ってclosed chainである必要ある？別にないのか？依存の向きだけあってればいい？
-- 型のなかに出現する変数の名前は基本そのままで。えーと？
-- {xtsはclosed chain} withHeader xts e {eの中でmap fst xs = [x1, ..., xn]はすべてlinearに出現する}
-- insert header for a closed chain
withHeader ::
     [(Identifier, CodePlus)] -- [(x1, t1), ..., (xn, tn)]  (closed chain)
  -> CodePlus
  -> WithEnv CodePlus
withHeader xts e = do
  (nm, e') <- distinguishCode (map fst xts) e
  withHeader' nm (reverse xts) e'

-- withHeader [] e = return e
-- withHeader ((x, t):xts) e = do
--   e' <- withHeader xts e
--   (xs, e'') <- distinguishCode x e'
--   case xs of
--     [] -> withHeaderAffine x t e''
--     [z] -> withHeaderLinear z x e''
--     (z1:z2:zs) -> withHeaderRelevant x t z1 z2 zs e''
type NameMap = Map.HashMap Identifier [Identifier]

withHeader' ::
     NameMap
  -> [(Identifier, CodePlus)] -- [(xn, tn), ..., (x1, t1)]  (reversed closed chain)
  -> CodePlus
  -> WithEnv CodePlus
withHeader' _ [] e = return e
withHeader' nm ((x, t):xts) e = do
  (nmT, t') <- distinguishCode (map fst xts) t
  let newNm = Map.unionWith (++) nmT nm
  e' <- withHeader'' newNm x t' e
  withHeader' newNm xts e'

-- insert header for a variable
withHeader'' ::
     NameMap -> Identifier -> CodePlus -> CodePlus -> WithEnv CodePlus
withHeader'' nm x t e =
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

-- distinguishData :: Identifier -> DataPlus -> WithEnv ([Identifier], DataPlus)
-- distinguishData z d@(ml, DataUpsilon x) =
--   if x /= z
--     then return ([], d)
--     else do
--       x' <- newNameWith z
--       return ([x'], (ml, DataUpsilon x'))
-- distinguishData z (ml, DataSigmaIntro mk ds) = do
--   (vss, ds') <- unzip <$> mapM (distinguishData z) ds
--   return (concat vss, (ml, DataSigmaIntro mk ds'))
-- distinguishData z (m, DataStructIntro dks) = do
--   let (ds, ks) = unzip dks
--   (vss, ds') <- unzip <$> mapM (distinguishData z) ds
--   return (concat vss, (m, DataStructIntro $ zip ds' ks))
-- distinguishData _ d = return ([], d)
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
  -- if zs `elem` map fst xts
  --   then return (vs1, (ml, CodeSigmaElim mk xts d' e))
  --   else do
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
distinguishCode zs (ml, CodeEnumElim d branchList) = do
  (vs, d') <- distinguishData zs d
  let (cs, es) = unzip branchList
  (vss, es') <- unzip <$> mapM (distinguishCode zs) es
  return (merge $ vs : vss, (ml, CodeEnumElim d' (zip cs es')))
distinguishCode zs (ml, CodeStructElim xts d e) = do
  (vs1, d') <- distinguishData zs d
  let zs' = filter (`notElem` map fst xts) zs
  -- if zs `elem` map fst xts
  --   then return (vs1, (ml, CodeStructElim xts d' e))
  --   else do
  (vs2, e') <- distinguishCode zs' e
  return (merge [vs1, vs2], (ml, CodeStructElim xts d' e'))

-- distinguishTheta :: Identifier -> Theta -> WithEnv ([Identifier], Theta)
-- distinguishTheta z (ThetaUnaryOp op lowType d) = do
--   (vs, d') <- distinguishData z d
--   return (vs, ThetaUnaryOp op lowType d')
-- distinguishTheta z (ThetaBinaryOp op lowType d1 d2) = do
--   (vs1, d1') <- distinguishData z d1
--   (vs2, d2') <- distinguishData z d2
--   return (vs1 ++ vs2, ThetaBinaryOp op lowType d1' d2')
-- distinguishTheta z (ThetaArrayAccess lowType d1 d2) = do
--   (vs1, d1') <- distinguishData z d1
--   (vs2, d2') <- distinguishData z d2
--   return (vs1 ++ vs2, ThetaArrayAccess lowType d1' d2')
-- distinguishTheta z (ThetaSysCall num ds) = do
--   (vss, ds') <- unzip <$> mapM (distinguishData z) ds
--   return (concat vss, ThetaSysCall num ds')
-- distinguishCode :: Identifier -> CodePlus -> WithEnv ([Identifier], CodePlus)
-- distinguishCode z (ml, CodeTheta theta) = do
--   (vs, theta') <- distinguishTheta z theta
--   return (vs, (ml, CodeTheta theta'))
-- distinguishCode z (ml, CodePiElimDownElim d ds) = do
--   (vs, d') <- distinguishData z d
--   (vss, ds') <- unzip <$> mapM (distinguishData z) ds
--   return (vs ++ concat vss, (ml, CodePiElimDownElim d' ds'))
-- distinguishCode z (ml, CodeSigmaElim mk xts d e) = do
--   (vs1, d') <- distinguishData z d
--   if z `elem` map fst xts
--     then return (vs1, (ml, CodeSigmaElim mk xts d' e))
--     else do
--       (vs2, e') <- distinguishCode z e
--       return (vs1 ++ vs2, (ml, CodeSigmaElim mk xts d' e'))
-- distinguishCode z (ml, CodeUpIntro d) = do
--   (vs, d') <- distinguishData z d
--   return (vs, (ml, CodeUpIntro d'))
-- distinguishCode z (ml, CodeUpElim x e1 e2) = do
--   (vs1, e1') <- distinguishCode z e1
--   if x == z
--     then return (vs1, (ml, CodeUpElim x e1' e2))
--     else do
--       (vs2, e2') <- distinguishCode z e2
--       return (vs1 ++ vs2, (ml, CodeUpElim x e1' e2'))
-- distinguishCode z (ml, CodeEnumElim d branchList) = do
--   (vs, d') <- distinguishData z d
--   let (cs, es) = unzip branchList
--   (vss, es') <- unzip <$> mapM (distinguishCode z) es
--   return (vs ++ concat vss, (ml, CodeEnumElim d' (zip cs es')))
-- distinguishCode z (ml, CodeStructElim xts d e) = do
--   (vs1, d') <- distinguishData z d
--   if z `elem` map fst xts
--     then return (vs1, (ml, CodeStructElim xts d' e))
--     else do
--       (vs2, e') <- distinguishCode z e
--       return (vs1 ++ vs2, (ml, CodeStructElim xts d' e'))
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
-- distinguishTheta :: Identifier -> Theta -> WithEnv ([Identifier], Theta)
-- distinguishTheta z (ThetaUnaryOp op lowType d) = do
--   (vs, d') <- distinguishData z d
--   return (vs, ThetaUnaryOp op lowType d')
-- distinguishTheta z (ThetaBinaryOp op lowType d1 d2) = do
--   (vs1, d1') <- distinguishData z d1
--   (vs2, d2') <- distinguishData z d2
--   return (vs1 ++ vs2, ThetaBinaryOp op lowType d1' d2')
-- distinguishTheta z (ThetaArrayAccess lowType d1 d2) = do
--   (vs1, d1') <- distinguishData z d1
--   (vs2, d2') <- distinguishData z d2
--   return (vs1 ++ vs2, ThetaArrayAccess lowType d1' d2')
-- distinguishTheta z (ThetaSysCall num ds) = do
--   (vss, ds') <- unzip <$> mapM (distinguishData z) ds
--   return (concat vss, ThetaSysCall num ds')
