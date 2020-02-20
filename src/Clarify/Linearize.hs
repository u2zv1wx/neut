{-# LANGUAGE OverloadedStrings #-}

module Clarify.Linearize
  ( linearize
  -- , toSNF
  ) where

import qualified Data.HashMap.Strict as Map

import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env
  --linearize' xts e

-- import Data.Term
-- linearizeの第1引数はeのなかでlinearに使用されるべき自由変数のリスト。closed chainでなければならないことに注意。
-- [x1, ..., xn] = map fst xtsとする。
-- {xtsはclosed chain} linearize {resultにおいて、x1, ..., xnはすべてlinearに出現する}
-- 「出現するならばlinearである」ってしたほうがいいのか？
-- linearize :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
-- linearize xts e = withHeader xts e
-- -- e' <- linearize xts eのとき、e'は、eとbeta-equivalentであり、かつ、xtsに含まれる変数の使用がlinearであるようなterm.
-- linearize' :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
-- linearize' xts (m, CodeSigmaElim ArrayKindVoidPtr yts d e)
--   -- let xts' = filter (\(x, _) -> x `elem` varCode e) xts
--   -- e' <- linearize (xts' ++ yts) e
--  = do
--   e' <- linearize yts e -- don't have to linearize e by yts
--   withHeader xts (m, CodeSigmaElim ArrayKindVoidPtr yts d e')
-- linearize' xts (m, CodeSigmaElim k ys d e)
--   -- let xts' = filter (\(x, _) -> x `elem` varCode e) xts
--   -- e' <- linearize xts' e
--   -- withHeader xts (m, CodeSigmaElim k ys d e')
--  = do
--   withHeader xts (m, CodeSigmaElim k ys d e)
-- linearize' xts (m, CodeUpElim z e1 e2)
--   -- let xts2' = filter (\(x, _) -> x `elem` varCode e2) xts
--   -- e2' <- linearize xts2' e2
--   -- let xts1' = filter (\(x, _) -> x `elem` varCode e1) xts
--   -- e1' <- linearize xts1' e1
--   -- withHeader xts (m, CodeUpElim z e1' e2')
--  = do
--   withHeader xts (m, CodeUpElim z e1 e2)
-- linearize' xts (m, CodeEnumElim d les) = do
--   let (ls, es) = unzip les
--   let xts' = filter (\(x, _) -> x `elem` concatMap varCode es) xts
--   es' <- mapM (linearize xts') es
--   withHeader xts (m, CodeEnumElim d $ zip ls es')
-- linearize' xts (m, CodeStructElim yks d e)
--   -- let xts' = filter (\(x, _) -> x `elem` varCode e) xts
--   -- e' <- linearize xts' e
--   -- withHeader xts (m, CodeStructElim yks d e')
--  = do
--   withHeader xts (m, CodeStructElim yks d e)
-- linearize' xts e = withHeader xts e -- e doesn't contain any CodePlus
-- insert header for a closed chain
linearize ::
     [(Identifier, CodePlus)] -- [(x1, t1), ..., (xn, tn)]  (closed chain)
  -> CodePlus
  -> WithEnv CodePlus
linearize xts e = do
  (nm, e') <- distinguishCode (map fst xts) e
  withHeader nm (reverse xts) e'

type NameMap = Map.HashMap Identifier [Identifier]

withHeader ::
     NameMap
  -> [(Identifier, CodePlus)] -- [(xn, tn), ..., (x1, t1)]  (reversed closed chain)
  -> CodePlus
  -> WithEnv CodePlus
withHeader _ [] e = return e -- ここでnamemapを返すようにする？
withHeader nm ((x, t):xts) e = do
  (nmT, t') <- distinguishCode (map fst xts) t
  let newNm = merge [nmT, nm]
  e' <- withHeader' newNm x t' e
  withHeader newNm xts e'

-- insert header for a variable
withHeader' :: NameMap -> Identifier -> CodePlus -> CodePlus -> WithEnv CodePlus
withHeader' nm x t e =
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
  -- return (vs, (ml, CodeEnumElim d' []))
-- distinguishCode zs (ml, CodeEnumElim xs d []) = do
--   (vs, d') <- distinguishData zs d
distinguishCode zs (ml, CodeEnumElim varInfo d branchList)
  -- p "enum-elim:"
  -- p' (ml, CodeEnumElim d branchList)
 = do
  (vs, d') <- distinguishData zs d
  let (from, to) = unzip varInfo
  (vss, to') <- unzip <$> mapM (distinguishData zs) to
  let varInfo' = zip from to'
  return (merge (vs : vss), (ml, CodeEnumElim varInfo' d' branchList)) -- let (cs, es) = unzip branchList
  -- vses <- mapM (distinguishCode zs) es
  -- (vs', es') <- foo zs vses
  -- -- (vss, es') <- unzip <$> mapM (distinguishCode zs) es -- fixme : 1つのbranchだけから変数情報をとるようにする。
  -- p "returning vs':"
  -- p' vs'
  -- return (merge [vs, vs'], (ml, CodeEnumElim varInfo d' (zip cs es'))) -- return (merge [vs, head vss], (ml, CodeEnumElim d' (zip cs es')))
  -- -- return (merge (vs : vss), (ml, CodeEnumElim d' (zip cs es'))) -- return (merge [vs, head vss], (ml, CodeEnumElim d' (zip cs es')))
distinguishCode zs (ml, CodeStructElim xts d e) = do
  (vs1, d') <- distinguishData zs d
  let zs' = filter (`notElem` map fst xts) zs
  (vs2, e') <- distinguishCode zs' e
  return (merge [vs1, vs2], (ml, CodeStructElim xts d' e'))

-- foo :: [Identifier] -> [(NameMap, CodePlus)] -> WithEnv (NameMap, [CodePlus])
-- foo _ [] = return (Map.empty, [])
-- foo _ [(nm, e)]
--   -- p "foo. nm:"
--   -- p' nm
--   -- p "e:"
--   -- p' e
--  = do
--   p "foo-last. e:"
--   p' e
--   return (nm, [e])
-- foo zs ((nm, e):nme:nmes)
--   -- p "foo (2). nm:"
--   -- p' nm
--   -- p "e:"
--   -- p' e
--  = do
--   (nm', es) <- foo zs $ nme : nmes
--   e' <- bar zs nm nm' e
--   p "foo-cont. e':"
--   p' e'
--   return (nm', e' : es)
-- bar :: [Identifier] -> NameMap -> NameMap -> CodePlus -> WithEnv CodePlus
-- bar [] _ _ e = return e
-- bar (z:zs) nm nm' e = do
--   e' <- bar zs nm nm' e
--   case (Map.lookup z nm, Map.lookup z nm') of
--     (Nothing, Nothing) -> return e'
--     (Just xs, Just xs')
--       | length xs == length xs' -> do
--         p "inslet. pair:"
--         p' $ zip xs xs'
--         -- xsのほうを消去すべきで。
--         return $ insLet (zip xs xs') e'
--     _
--       -- p "e:"
--       -- p' e'
--       -- p "nm:"
--       -- p' nm
--       -- p "nm':"
--       -- p' nm'
--      -> do
--       throwError' "[compiler bug] Linearize.bar."
-- insLet :: [(Identifier, Identifier)] -> CodePlus -> CodePlus
-- insLet [] e = e
-- insLet ((x, x'):xxs) e =
--   ( emptyMeta
--   , CodeUpElim
--       x
--       (emptyMeta, CodeUpIntro (emptyMeta, DataUpsilon x'))
--       (insLet xxs e))
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
-- this function adjusts variable occurrence of each branch in EnumElim:
--   case d of
--     c1 -> (x, x, y)
--     c2 -> (y, z)
--     c3 -> 3
--     c4 -> w
--
--   ~>
--
--   case d of
--     c1 -> let _ := z in
--           let _ := w in
--           (x, x, y)
--     c2 -> let _ := x in
--           let _ := x in
--           let _ := w in
--           (y, z)
--     c3 -> let _ := x in
--           let _ := x in
--           let _ := y in
--           let _ := z in
--           let _ := w in
--           3
--     c4 -> let _ := x in
--           let _ := x in
--           let _ := y in
--           let _ := z in
--           w
--
-- I define such EnumElim to be supremum-normal (because we're computing the supremum of variable sets).
-- I also define a term to be supremum-normal-form (SNF) when all the EnumElim in the term is supremum-normal.
-- type VarInfo = Map.HashMap Identifier Int
-- toSNF :: TermPlus -> WithEnv TermPlus
-- toSNF e = snd <$> toSNF' e
-- toSNF' :: TermPlus -> WithEnv (VarInfo, TermPlus)
-- toSNF' (m, TermTau l) = return (Map.empty, (m, TermTau l))
-- toSNF' (m, TermUpsilon x) = return (Map.singleton x 1, (m, TermUpsilon x))
-- toSNF' (m, TermPi mls xts t) = do
--   (vi, xts', t') <- toSNFBinder xts t
--   return (vi, (m, TermPi mls xts' t'))
-- toSNF' (m, TermPiIntro xts e) = do
--   (vi, xts', e') <- toSNFBinder xts e
--   return (vi, (m, TermPiIntro xts' e'))
-- toSNF' (m, TermPiElim e es) = do
--   (vi, e') <- toSNF' e
--   (vis, es') <- unzip <$> mapM toSNF' es
--   return (addVI (vi : vis), (m, TermPiElim e' es'))
-- toSNF' (m, TermSigma xts) = do
--   (vi, xts') <- toSNFSigma xts
--   -- (vi, xts') <- toSNF'' xts
--   return (vi, (m, TermSigma xts'))
-- toSNF' (m, TermSigmaIntro t es) = do
--   (vi, t') <- toSNF' t
--   (vis, es') <- unzip <$> mapM toSNF' es
--   return (addVI (vi : vis), (m, TermSigmaIntro t' es'))
-- toSNF' (m, TermSigmaElim t xts e1 e2) = do
--   (vi3, t') <- toSNF' t
--   (vi1, e1') <- toSNF' e1
--   (vi2, xts', e2') <- toSNFBinder xts e2
--   return (addVI [vi1, vi2, vi3], (m, TermSigmaElim t' xts' e1' e2'))
-- toSNF' (m, TermIter (mx, x, t) xts e) = do
--   insTypeEnv' x t
--   (vi1, t') <- toSNF' t
--   (vi2, xts', e') <- toSNFBinder xts e
--   let vi2' = Map.delete x vi2
--   return (addVI [vi1, vi2'], (m, TermIter (mx, x, t') xts' e'))
-- toSNF' (m, TermConst x) = return (Map.empty, (m, TermConst x))
-- toSNF' (m, TermConstDecl (mx, x, t) e) = do
--   (vi1, t') <- toSNF' t
--   (vi2, e') <- toSNF' e
--   return (addVI [vi1, vi2], (m, TermConstDecl (mx, x, t') e'))
-- toSNF' (m, TermFloat16 x) = return (Map.empty, (m, TermFloat16 x))
-- toSNF' (m, TermFloat32 x) = return (Map.empty, (m, TermFloat32 x))
-- toSNF' (m, TermFloat64 x) = return (Map.empty, (m, TermFloat64 x))
-- toSNF' (m, TermEnum x) = return (Map.empty, (m, TermEnum x))
-- toSNF' (m, TermEnumIntro l) = return (Map.empty, (m, TermEnumIntro l))
-- toSNF' (m, TermEnumElim (e, t) branchList) = do
--   (vi1, t') <- toSNF' t
--   (vi2, e') <- toSNF' e
--   let (caseList, es) = unzip branchList
--   vies <- mapM toSNF' es
--   let vis = map fst vies
--   let vi = supVI vis
--   es' <- mapM (uncurry $ toSNFBranch vi) vies
--   let vi' = addVI [vi1, vi2, vi]
--   return (vi', (m, TermEnumElim (e', t') (zip caseList es')))
-- toSNF' (m, TermArray dom k) = do
--   (vi, dom') <- toSNF' dom
--   return (vi, (m, TermArray dom' k))
-- toSNF' (m, TermArrayIntro k es) = do
--   (vis, es') <- unzip <$> mapM toSNF' es
--   return (addVI vis, (m, TermArrayIntro k es'))
-- toSNF' (m, TermArrayElim mk xts v e) = do
--   (vi1, v') <- toSNF' v
--   (vi2, xts', e') <- toSNFBinder xts e
--   return (addVI [vi1, vi2], (m, TermArrayElim mk xts' v' e'))
-- toSNF' (m, TermStruct ts) = return (Map.empty, (m, TermStruct ts))
-- toSNF' (m, TermStructIntro ets) = do
--   let (es, ts) = unzip ets
--   (vis, es') <- unzip <$> mapM toSNF' es
--   return (addVI vis, (m, TermStructIntro $ zip es' ts))
-- toSNF' (m, TermStructElim xts v e) = do
--   (vi1, v') <- toSNF' v
--   (vi2, e') <- toSNF' e
--   let vi2' = filterVI (map (\(_, x, _) -> x) xts) vi2
--   return (addVI [vi1, vi2'], (m, TermStructElim xts v' e'))
-- toSNFBinder ::
--      [(Meta, Identifier, TermPlus)]
--   -> TermPlus
--   -> WithEnv (VarInfo, [(Meta, Identifier, TermPlus)], TermPlus)
-- toSNFBinder [] e = do
--   (vi, e') <- toSNF' e
--   return (vi, [], e')
-- toSNFBinder ((m, x, t):xts) e = do
--   insTypeEnv' x t
--   (vi1, xts', e') <- toSNFBinder xts e
--   let vi1' = Map.delete x vi1
--   (vi2, t') <- toSNF' t
--   return (addVI [vi1', vi2], (m, x, t') : xts', e')
-- toSNFSigma ::
--      [(Meta, Identifier, TermPlus)]
--   -> WithEnv (VarInfo, [(Meta, Identifier, TermPlus)])
-- toSNFSigma [] = return (Map.empty, [])
-- toSNFSigma ((m, x, t):xts) = do
--   insTypeEnv' x t
--   (vi1, xts') <- toSNFSigma xts
--   let vi1' = Map.delete x vi1
--   (vi2, t') <- toSNF' t
--   return (addVI [vi1', vi2], (m, x, t') : xts')
-- toSNFBranch :: VarInfo -> VarInfo -> TermPlus -> WithEnv TermPlus
-- toSNFBranch sup vi e = toSNFBranch' (Map.toList $ diffVI sup vi) e
-- toSNFBranch' :: [(Identifier, Int)] -> TermPlus -> WithEnv TermPlus
-- toSNFBranch' [] e = return e
-- toSNFBranch' ((x, i):xis) e = do
--   e' <- toSNFBranch' xis e
--   t <- lookupTypeEnv' x
--   insHeader x t i e'
-- addVI :: [VarInfo] -> VarInfo
-- addVI = foldr (Map.unionWith (+)) Map.empty
-- supVI :: [VarInfo] -> VarInfo
-- supVI = foldr (Map.unionWith max) Map.empty
-- diffVI :: VarInfo -> VarInfo -> VarInfo
-- diffVI vi1 vi2 = Map.differenceWith (\i1 i2 -> Just (i1 - i2)) vi1 vi2
-- filterVI :: [Identifier] -> VarInfo -> VarInfo
-- filterVI [] vi = vi
-- filterVI (x:xs) vi = Map.delete x $ filterVI xs vi
-- -- insHeader x t i e ~>
-- --   let (_ : t) := x in   --
-- --   ...                   -- i times
-- --   let (_ : t) := x in   --
-- --   e
-- insHeader :: Identifier -> TermPlus -> Int -> TermPlus -> WithEnv TermPlus
-- insHeader _ _ 0 e = return e
-- insHeader x t i e = do
--   e' <- insHeader x t (i - 1) e
--   h <- newNameWith x
--   let m = fst e
--   return (m, TermPiElim (m, TermPiIntro [(m, h, t)] e') [(m, TermUpsilon x)])
