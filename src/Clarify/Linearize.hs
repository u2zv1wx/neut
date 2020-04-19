module Clarify.Linearize
  ( linearize
  ) where

import qualified Data.IntMap as IntMap

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

type NameMap = IntMap.IntMap [Identifier]

linearize' ::
     NameMap
  -> [(Identifier, CodePlus)] -- [(xn, tn), ..., (x1, t1)]  (reversed closed chain)
  -> CodePlus
  -> WithEnv CodePlus
linearize' _ [] e = return e
linearize' nm ((x, t):xts) e = do
  (nmT, t') <- distinguishCode (map fst xts) t
  let newNm = merge [nmT, nm]
  e' <- withHeader newNm x t' e
  linearize' newNm xts e'

-- insert header for a variable
withHeader :: NameMap -> Identifier -> CodePlus -> CodePlus -> WithEnv CodePlus
withHeader nm x t e =
  case IntMap.lookup (asInt x) nm of
    Nothing -> withHeaderAffine x t e
    Just [] -> raiseCritical' $ "impossible. x: " <> asText' x
    Just [z] -> withHeaderLinear z x e
    Just (z1:z2:zs) -> withHeaderRelevant x t z1 z2 zs e

-- withHeaderAffine x t e ~>
--   bind _ :=
--     bind exp := t^# in        --
--     exp @ (0, x) in           -- AffineApp
--   e
--
-- withHeaderAffine x t e ~>
--   bind _ :=
--     bind exp := t^# in        -- AffineApp
--     exp @ (0, x) in           --
--   e
-- 変数xに型t由来のaffineを適用して破棄する。
withHeaderAffine :: Identifier -> CodePlus -> CodePlus -> WithEnv CodePlus
withHeaderAffine x t e@(m, _) = do
  hole <- newNameWith' "unit"
  discardUnusedVar <- toAffineApp m x t
  return (m, CodeUpElim hole discardUnusedVar e)

-- withHeaderLinear z x e ~>
--   bind z := return x in
--   e
-- renameするだけ。
withHeaderLinear :: Identifier -> Identifier -> CodePlus -> WithEnv CodePlus
withHeaderLinear z x e@(m, _) =
  return (m, CodeUpElim z (m, CodeUpIntro (m, DataUpsilon x)) e)

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
     Identifier
  -> CodePlus
  -> Identifier
  -> Identifier
  -> [Identifier]
  -> CodePlus
  -> WithEnv CodePlus
withHeaderRelevant x t x1 x2 xs e@(m, _) = do
  (expVarName, expVar) <- newDataUpsilonWith m "exp"
  linearChain <- toLinearChain $ x : x1 : x2 : xs
  rel <- withHeaderRelevant' t expVar linearChain e
  return (m, CodeUpElim expVarName t rel)

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
withHeaderRelevant' ::
     CodePlus -> DataPlus -> LinearChain -> CodePlus -> WithEnv CodePlus
withHeaderRelevant' _ _ [] cont = return cont
withHeaderRelevant' t expVar ((x, (x1, x2)):chain) cont@(m, _) = do
  cont' <- withHeaderRelevant' t expVar chain cont
  (sigVarName, sigVar) <- newDataUpsilonWith m "sig"
  return $
    ( m
    , CodeUpElim
        sigVarName
        ( m
        , CodePiElimDownElim
            expVar
            [(m, DataEnumIntro (EnumValueIntS 64 1)), (m, DataUpsilon x)])
        (m, sigmaElim [x1, x2] sigVar cont'))

merge :: [NameMap] -> NameMap
merge [] = IntMap.empty
merge (m:ms) = IntMap.unionWith (++) m $ merge ms

distinguishData :: [Identifier] -> DataPlus -> WithEnv (NameMap, DataPlus)
distinguishData zs d@(ml, DataUpsilon x) =
  if x `notElem` zs
    then return (IntMap.empty, d)
    else do
      x' <- newNameWith x
      return (IntMap.singleton (asInt x) [x'], (ml, DataUpsilon x'))
distinguishData zs (ml, DataSigmaIntro mk ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge vss, (ml, DataSigmaIntro mk ds'))
distinguishData zs (m, DataStructIntro dks) = do
  let (ds, ks) = unzip dks
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge vss, (m, DataStructIntro $ zip ds' ks))
distinguishData _ d = return (IntMap.empty, d)

distinguishCode :: [Identifier] -> CodePlus -> WithEnv (NameMap, CodePlus)
distinguishCode zs (ml, CodeConst theta) = do
  (vs, theta') <- distinguishConst zs theta
  return (vs, (ml, CodeConst theta'))
distinguishCode zs (ml, CodePiElimDownElim d ds) = do
  (vs, d') <- distinguishData zs d
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge $ vs : vss, (ml, CodePiElimDownElim d' ds'))
distinguishCode zs (ml, CodeSigmaElim mk xs d e) = do
  (vs1, d') <- distinguishData zs d
  let zs' = filter (`notElem` xs) zs
  (vs2, e') <- distinguishCode zs' e
  return (merge [vs1, vs2], (ml, CodeSigmaElim mk xs d' e'))
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
  let (from, to) = unzip $ IntMap.toList varInfo
  (vss, to') <- unzip <$> mapM (distinguishData zs) to
  let varInfo' = IntMap.fromList $ zip from to'
  return (merge (vs : vss), (ml, CodeEnumElim varInfo' d' branchList))
distinguishCode zs (ml, CodeStructElim xts d e) = do
  (vs1, d') <- distinguishData zs d
  let zs' = filter (`notElem` map fst xts) zs
  (vs2, e') <- distinguishCode zs' e
  return (merge [vs1, vs2], (ml, CodeStructElim xts d' e'))
distinguishCode zs (ml, CodeCase varInfo d branchList) = do
  (vs, d') <- distinguishData zs d
  let (from, to) = unzip $ IntMap.toList varInfo
  (vss, to') <- unzip <$> mapM (distinguishData zs) to
  let varInfo' = IntMap.fromList $ zip from to'
  return (merge (vs : vss), (ml, CodeCase varInfo' d' branchList))

distinguishConst :: [Identifier] -> Const -> WithEnv (NameMap, Const)
distinguishConst zs (ConstUnaryOp op d) = do
  (vs, d') <- distinguishData zs d
  return (vs, ConstUnaryOp op d')
distinguishConst zs (ConstBinaryOp op d1 d2) = do
  (vs1, d1') <- distinguishData zs d1
  (vs2, d2') <- distinguishData zs d2
  return (merge [vs1, vs2], ConstBinaryOp op d1' d2')
distinguishConst zs (ConstArrayAccess lowType d1 d2) = do
  (vs1, d1') <- distinguishData zs d1
  (vs2, d2') <- distinguishData zs d2
  return (merge [vs1, vs2], ConstArrayAccess lowType d1' d2')
distinguishConst zs (ConstSysCall num ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData zs) ds
  return (merge vss, ConstSysCall num ds')
