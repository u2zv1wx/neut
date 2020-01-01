module Clarify.Linearize
  ( linearize
  , cartesianImmediate
  , cartesianUniv
  , cartesianSigma
  , bindLet
  , returnCartesianImmediate
  , returnCartesianUniv
  , returnUpsilon
  , returnArrayType
  , returnClosureType
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Prelude hiding (pi)

import Data.Basic
import Data.Code
import Data.Env

-- import Data.Term
-- import Reduce.Term
import qualified Text.Show.Pretty as Pr

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

returnUpsilon :: Identifier -> CodePlus
returnUpsilon x = (emptyMeta, CodeUpIntro (emptyMeta, DataUpsilon x))

returnArrayType :: Meta -> WithEnv CodePlus
returnArrayType ml = do
  tau <- cartesianImmediate ml
  (arrVarName, arrVar) <- newDataUpsilonWith "arr"
  let retTau = (ml, CodeUpIntro tau)
  let retArrVar = (ml, CodeUpIntro arrVar)
  v <-
    cartesianSigma
      "array-closure"
      ml
      [Right (arrVarName, retTau), Left retArrVar]
  return (ml, CodeUpIntro v)

returnClosureType :: Meta -> WithEnv CodePlus
returnClosureType m = do
  imm <- cartesianImmediate m
  tau <- cartesianUniv m
  (envVarName, envVar) <- newDataUpsilonWith "env"
  let retUnivType = (m, CodeUpIntro tau)
  let retImmType = (m, CodeUpIntro imm)
  let retEnvVar = (m, CodeUpIntro envVar)
  closureType <-
    cartesianSigma
      "closure"
      m
      [Right (envVarName, retUnivType), Left retEnvVar, Left retImmType]
  return (m, CodeUpIntro closureType)

returnCartesianImmediate :: WithEnv CodePlus
returnCartesianImmediate = do
  v <- cartesianImmediate emptyMeta
  return (emptyMeta, CodeUpIntro v)

returnCartesianUniv :: WithEnv CodePlus
returnCartesianUniv = do
  v <- cartesianUniv emptyMeta
  return (emptyMeta, CodeUpIntro v)

cartesianImmediate :: Meta -> WithEnv DataPlus
cartesianImmediate m = do
  aff <- affineImmediate m
  rel <- relevantImmediate m
  return (m, DataSigmaIntro [aff, rel])

affineImmediate :: Meta -> WithEnv DataPlus
affineImmediate m = do
  cenv <- gets codeEnv
  let thetaName = "affine-immediate"
  let theta = (m, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      immVarName <- newNameWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro []))
      return theta

relevantImmediate :: Meta -> WithEnv DataPlus
relevantImmediate m = do
  cenv <- gets codeEnv
  let thetaName = "relevant-immediate"
  let theta = (m, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (immVarName, immVar) <- newDataUpsilonWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro [immVar, immVar]))
      return theta

cartesianUniv :: Meta -> WithEnv DataPlus
cartesianUniv m = do
  aff <- affineUniv m
  rel <- relevantUniv m
  return (m, DataSigmaIntro [aff, rel])

-- \x -> let (_, _) := x in unit
affineUniv :: Meta -> WithEnv DataPlus
affineUniv m = do
  cenv <- gets codeEnv
  let thetaName = "affine-univ"
  let theta = (m, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (univVarName, univVar) <- newDataUpsilonWith "univ"
      affVarName <- newNameWith "var"
      relVarName <- newNameWith "var"
      retImmType <- returnCartesianImmediate
      insCodeEnv
        thetaName
        [univVarName]
        -- let (a, b) := x in return ()
        ( emptyMeta
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            (emptyMeta, CodeUpIntro (emptyMeta, DataSigmaIntro [])))
      return theta

relevantUniv :: Meta -> WithEnv DataPlus
relevantUniv m = do
  cenv <- gets codeEnv
  let thetaName = "relevant-univ"
  let theta = (m, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (univVarName, univVar) <- newDataUpsilonWith "univ"
      (affVarName, affVar) <- newDataUpsilonWith "univ-aff"
      (relVarName, relVar) <- newDataUpsilonWith "univ-rel"
      retImmType <- returnCartesianImmediate
      insCodeEnv
        thetaName
        [univVarName]
        -- let (a, b) := x in return ((a, b), (a, b))
        ( emptyMeta
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            ( emptyMeta
            , CodeUpIntro
                ( emptyMeta
                , DataSigmaIntro
                    [ (emptyMeta, DataSigmaIntro [affVar, relVar])
                    , (emptyMeta, DataSigmaIntro [affVar, relVar])
                    ])))
      return theta

cartesianSigma ::
     Identifier
  -> Meta
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
cartesianSigma thetaName m mxts = do
  aff <- affineSigma ("affine-" ++ thetaName) m mxts
  rel <- relevantSigma ("relevant-" ++ thetaName) m mxts
  return (m, DataSigmaIntro [aff, rel])

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- affineSigma NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
--   update CodeEnv with NAME ~> (thunk LAM), where LAM is:
--   lam z.
--     let (x1, ..., xn) := z in
--     <LINEARIZE_HEADER for x1, .., xn> in                     ---
--     bind y1 :=                                    ---        ---
--       bind f1 = t1 in              ---            ---        ---
--       let (aff-1, rel-1) = f1 in   ---  APP-1     ---        ---
--       aff-1 @ x1 in                ---            ---        ---
--     ...                                           ---  body  ---  body'
--     bind yn :=                                    ---        ---
--       bind fn = tn in              ---            ---        ---
--       let (aff-n, rel-n) := fn in  ---  APP-n     ---        ---
--       aff-n @ xn in                ---            ---        ---
--     return ()                                     ---        ---
--
-- (Note that sigma-elim for yi is not necessary since all of them are units.)
affineSigma ::
     Identifier
  -> Meta
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
affineSigma thetaName m mxts = do
  cenv <- gets codeEnv
  let theta = (m, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      xts <- mapM supplyName mxts
      (z, varZ) <- newDataUpsilonWith "arg"
      -- As == [APP-1, ..., APP-n]   (`a` here stands for `app`)
      as <- forM xts $ \(x, e) -> toAffineApp m x e
      ys <- mapM (const $ newNameWith "arg") xts
      let body = bindLet (zip ys as) (m, CodeUpIntro (m, DataSigmaIntro []))
      body' <- linearize xts body
      insCodeEnv thetaName [z] (m, CodeSigmaElim xts varZ body')
      -- when (thetaName == "affine-closure") $ do
      --   p "affine-closure"
      --   p' (m, CodeSigmaElim xts varZ body')
      return theta

-- (Assuming `ti` = `return di` for some `di` such that `xi : di`)
-- relevantSigma NAME LOC [(x1, t1), ..., (xn, tn)]   ~>
--   update CodeEnv with NAME ~> (thunk LAM), where LAM is:
--   lam z.
--     let (x1, ..., xn) := z in
--     <LINEARIZE_HEADER for x1, .., xn> in                                      ---
--     bind pair-1 :=                                                  ---       ---
--       bind f1 = t1 in              ---                              ---       ---
--       let (aff-1, rel-1) = f1 in   ---  APP-1                       ---       ---
--       rel-1 @ x1 in                ---                              ---       ---
--     ...                                                             ---       ---
--     bind pair-n :=                                                  --- body  --- body'
--       bind fn = tn in              ---                              ---       ---
--       let (aff-n, rel-n) := fn in  ---  APP-n                       ---       ---
--       rel-n @ xn in                ---                              ---       ---
--     let (p11, p12) := pair-1 in               ---                   ---       ---
--     ...                                       ---  TRANSPOSED-PAIR  ---       ---
--     let (pn1, pn2) := pair-n in               ---                   ---       ---
--     return ((p11, ..., pn1), (p12, ..., pn2)) ---                   ---       ---
relevantSigma ::
     Identifier
  -> Meta
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
relevantSigma thetaName m mxts = do
  cenv <- gets codeEnv
  let theta = (m, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      xts <- mapM supplyName mxts
      (z, varZ) <- newDataUpsilonWith "arg"
      -- as == [APP-1, ..., APP-n]
      as <- forM xts $ \(x, e) -> toRelevantApp m x e
      -- pairVarNameList == [pair-1, ...,  pair-n]
      (pairVarNameList, pairVarTypeList) <- unzip <$> mapM toPairInfo xts
      transposedPair <- transposeSigma pairVarTypeList
      let body = bindLet (zip pairVarNameList as) transposedPair
      body' <- linearize xts body
      insCodeEnv thetaName [z] (m, CodeSigmaElim xts varZ body')
      return theta

toPairInfo ::
     (Identifier, CodePlus) -> WithEnv (Identifier, (DataPlus, CodePlus))
toPairInfo (_, t) = do
  (name, var) <- newDataUpsilonWith "pair"
  return (name, (var, t))

-- transposeSigma [d1, ..., dn] :=
--   let (x1, y1) := d1 in
--   ...
--   let (xn, yn) := dn in
--   return ((x1, ..., xn), (y1, ..., yn))
transposeSigma :: [(DataPlus, CodePlus)] -> WithEnv CodePlus
transposeSigma ds = do
  (xVarNameList, xVarList) <-
    unzip <$> mapM (const $ newDataUpsilonWith "sig-x") ds
  (yVarNameList, yVarList) <-
    unzip <$> mapM (const $ newDataUpsilonWith "sig-y") ds
  return $
    bindSigmaElim (zip (zip xVarNameList yVarNameList) ds) $
    ( emptyMeta
    , CodeUpIntro
        ( emptyMeta
        , DataSigmaIntro
            [ (emptyMeta, DataSigmaIntro xVarList)
            , (emptyMeta, DataSigmaIntro yVarList)
            ]))

bindSigmaElim ::
     [((Identifier, Identifier), (DataPlus, CodePlus))] -> CodePlus -> CodePlus
bindSigmaElim [] cont = cont
bindSigmaElim (((x, y), (d, t)):xyds) cont = do
  let cont' = bindSigmaElim xyds cont
  (fst cont', CodeSigmaElim [(x, t), (y, t)] d cont')

-- toAffineApp ML x e ~>
--   bind f := e in
--   let (aff, rel) := f in
--   aff @ x
toAffineApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toAffineApp m x e = do
  (expVarName, expVar) <- newDataUpsilonWith "exp"
  (affVarName, affVar) <- newDataUpsilonWith "aff"
  (relVarName, _) <- newDataUpsilonWith "rel"
  retImmType <- returnCartesianImmediate
  return
    ( m
    , CodeUpElim
        expVarName
        e
        ( emptyMeta
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (m, CodePiElimDownElim affVar [toDataUpsilon (x, fst e)])))

-- toRelevantApp ML x e ~>
--   bind f := e in
--   let (aff, rel) := f in
--   rel @ x
toRelevantApp :: Meta -> Identifier -> CodePlus -> WithEnv CodePlus
toRelevantApp m x e = do
  (expVarName, expVar) <- newDataUpsilonWith "rel-app-exp"
  (affVarName, _) <- newDataUpsilonWith "rel-app-aff"
  (relVarName, relVar) <- newDataUpsilonWith "rel-app-rel"
  retImmType <- returnCartesianImmediate
  return
    ( m
    , CodeUpElim
        expVarName
        e
        ( m
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (m, CodePiElimDownElim relVar [toDataUpsilon (x, fst e)])))

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Right (x, t)) = return (x, t)
supplyName (Left t) = do
  x <- newNameWith "unused-sigarg"
  return (x, t)

bindLet :: [(Identifier, CodePlus)] -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = do
  let cont' = bindLet xes cont
  (fst cont', CodeUpElim x e cont')
