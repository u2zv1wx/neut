module Clarify.Linearize
  ( linearize
  ) where

import Control.Monad.Except
import Data.List
import Prelude hiding (pi)

import Clarify.Utility
import Data.Basic
import Data.Code
import Data.Env

-- e' <- linearize xts eのとき、e'は、eとbeta-equivalentであり、かつ、xtsに含まれる変数の使用がpractically linearであるようなterm.
-- linearizeの第1引数はeのなかでlinearに使用されるべき自由変数のリスト。
linearize :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
linearize xts (m, CodeSigmaElim yts d e) = do
  let xts' = filter (\(x, _) -> x `elem` varCode e) xts
  -- xts'は、xtsのうち実際にeで使用されている変数の集合。実際に使用されているのでeのなかでcopyが起こりうる。
  -- eのなかで使用されていないものを放置するのは、それらはなるべく早くfreeしたほうが空間的に効率的だから。
  -- copyは遅ければ遅いほど効率的だし、freeは早ければ早いほど効率的。
  -- なお、sigmaの型はすべてclosedなので、ytsのなかに変な自由変数が現れたりすることはない。
  -- つまり、yts = [(y1, ret t1), ..., (yn, ret tn)]とおくと、Sigma (y1 : t1, ..., yn : tn)は
  -- closedなsigmaになっている。
  -- yiを自由変数としてふくんだtiがeのなかでどんだけ使われようが、それらはlinearize (...) eによってlinearizeされるから
  -- yiの自由変数としての使用を心配する必要はない。
  p "linearize-sigma-cont-with:"
  p' $ map fst $ xts' ++ yts
  e' <- linearize (xts' ++ yts) e
  -- eのなかで使用されておらず、かつdのなかでも使用されていないものなども、ここで適切にheaderを挿入することで対応する。
  withHeader xts (m, CodeSigmaElim yts d e')
linearize xts (m, CodeUpElim z e1 e2) = do
  let xts2' = filter (\(x, _) -> x `elem` varCode e2) xts
  -- zはe2のなかでlinearに使用されることが既知なので放置でよい。
  -- つまり、zについてのlinearizeの必要がないのでxts2' ++ [z]でなくxts2'を引数として与えれば十分。
  e2' <- linearize xts2' e2
  let xts1' = filter (\(x, _) -> x `elem` varCode e1) xts
  e1' <- linearize xts1' e1
  withHeader xts (m, CodeUpElim z e1' e2')
linearize xts (m, CodeEnumElim d les) = do
  let (ls, es) = unzip les
  -- xts'は、xtsのうちすくなくともひとつのbranchにおいて使われているような変数の集合。
  -- どのbranchでも使用されていない変数はbranchの外側で先にfreeしてしまう。
  let xts' = filter (\(x, _) -> x `elem` concatMap varCode es) xts
  es' <- mapM (linearize xts') es
  withHeader xts (m, CodeEnumElim d $ zip ls es')
linearize xts e = withHeader xts e -- eのなかにCodePlusが含まれないケース

-- eのなかでxtsがpractically linearになるよう適切にheaderを挿入する。
withHeader :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
withHeader xts e = do
  p "distinguishing: "
  p' $ map fst xts
  (xtzss, e') <- distinguish xts e
  withHeader' xtzss e'

withHeader' ::
     [(Identifier, CodePlus, [Identifier])] -> CodePlus -> WithEnv CodePlus
withHeader' [] e = return e
withHeader' ((x, t, []):xtzss) e = do
  e' <- withHeader' xtzss e
  withHeaderAffine x t e'
withHeader' ((x, _, [z]):xtzss) e = do
  e' <- withHeader' xtzss e -- already linear.
  let m = emptyMeta
  return (m, CodeUpElim z (m, CodeUpIntro (m, DataUpsilon x)) e')
withHeader' ((x, t, (z1:z2:zs)):xtzss) e = do
  e' <- withHeader' xtzss e
  withHeaderRelevant x t z1 z2 zs e'

-- withHeaderAffine x t e ~>
--   bind _ :=
--     bind exp := t^# in        --
--     let (aff, rel) := exp in  -- AffineApp
--     aff @ x in                --
--   e
withHeaderAffine :: Identifier -> CodePlus -> CodePlus -> WithEnv CodePlus
withHeaderAffine x t e = do
  hole <- newNameWith "unit"
  discardUnusedVar <- toAffineApp emptyMeta x t
  return (emptyMeta, CodeUpElim hole discardUnusedVar e)

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
  -- xそのものの型はtなのでこれを利用？
  -- このtのなかに自由変数があるとやばそうじゃない？
  -- 別にSigmaElimにannotationをあたえていても、それを使うってわけじゃないから問題ないのか。
  rel <- withHeaderRelevant' t relVar linearChain e
  retImmType <- returnCartesianImmediate
  return
    ( ml
    , CodeUpElim
        expVarName
        t
        ( ml
        , CodeSigmaElim
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
        (m, CodeSigmaElim [(x1, t), (x2, t)] sigVar cont'))

-- distinguish [(x1, t1), ..., (xn, tn)] eは、は、eにおけるxiの出現をすべて新しい名前で置き換え、そうして得られたtermをe'として、
-- ([(x1, t1, {list-of-new-names-for-x1}), ..., (xm, tm, {list-of-new-names-for-xm})], e')を返す。
distinguish ::
     [(Identifier, CodePlus)]
  -> CodePlus
  -> WithEnv ([(Identifier, CodePlus, [Identifier])], CodePlus)
distinguish [] e = return ([], e)
distinguish ((x, t):xts) e = do
  (xtzss, e') <- distinguish xts e
  (xs, e'') <- distinguishCode x e'
  return ((x, t, xs) : xtzss, e'')

distinguishData :: Identifier -> DataPlus -> WithEnv ([Identifier], DataPlus)
distinguishData z d@(ml, DataUpsilon x) =
  if x /= z
    then return ([], d)
    else do
      x' <- newNameWith z
      return ([x'], (ml, DataUpsilon x'))
distinguishData z (ml, DataSigmaIntro ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData z) ds
  return (concat vss, (ml, DataSigmaIntro ds'))
distinguishData _ d = return ([], d)

-- distinguishのときにtype annotationはいじらなくていいんだろうか？大丈夫そう？
-- 大丈夫そう。だって、annotationのほうは実際のコードには反映されていないから。
-- ここのannotationはあくまでlinearizeをおこなうときに必要な情報を保持しているだけで、実際のコードとは関係ない。
distinguishCode :: Identifier -> CodePlus -> WithEnv ([Identifier], CodePlus)
distinguishCode z (ml, CodeTheta theta) = do
  (vs, theta') <- distinguishTheta z theta
  return (vs, (ml, CodeTheta theta'))
distinguishCode z (ml, CodePiElimDownElim d ds) = do
  (vs, d') <- distinguishData z d
  (vss, ds') <- unzip <$> mapM (distinguishData z) ds
  return (vs ++ concat vss, (ml, CodePiElimDownElim d' ds'))
distinguishCode z (ml, CodeSigmaElim xts d e) = do
  (vs1, d') <- distinguishData z d
  if z `elem` map fst xts
    then return (vs1, (ml, CodeSigmaElim xts d' e))
    else do
      (vs2, e') <- distinguishCode z e
      -- このときはxtsの要素のそれぞれについてeをdistinguishする必要があるはず？
      return (vs1 ++ vs2, (ml, CodeSigmaElim xts d' e'))
distinguishCode z (ml, CodeUpIntro d) = do
  (vs, d') <- distinguishData z d
  return (vs, (ml, CodeUpIntro d'))
distinguishCode z (ml, CodeUpElim x e1 e2) = do
  (vs1, e1') <- distinguishCode z e1
  if x == z
    then return (vs1, (ml, CodeUpElim x e1' e2))
    else do
      (vs2, e2') <- distinguishCode z e2
      return (vs1 ++ vs2, (ml, CodeUpElim x e1' e2'))
distinguishCode z (ml, CodeEnumElim d branchList) = do
  (vs, d') <- distinguishData z d
  let (cs, es) = unzip branchList
  (vss, es') <- unzip <$> mapM (distinguishCode z) es
  return (vs ++ concat vss, (ml, CodeEnumElim d' (zip cs es')))
distinguishCode z (ml, CodeArrayElim k d1 d2) = do
  (vs1, d1') <- distinguishData z d1
  (vs2, d2') <- distinguishData z d2
  return (vs1 ++ vs2, (ml, CodeArrayElim k d1' d2'))

distinguishTheta :: Identifier -> Theta -> WithEnv ([Identifier], Theta)
distinguishTheta z (ThetaUnaryOp op lowType d) = do
  (vs, d') <- distinguishData z d
  return (vs, ThetaUnaryOp op lowType d')
distinguishTheta z (ThetaBinaryOp op lowType d1 d2) = do
  (vs1, d1') <- distinguishData z d1
  (vs2, d2') <- distinguishData z d2
  return (vs1 ++ vs2, ThetaBinaryOp op lowType d1' d2')
distinguishTheta z (ThetaSysCall num ds) = do
  (vss, ds') <- unzip <$> mapM (distinguishData z) ds
  return (concat vss, ThetaSysCall num ds')
