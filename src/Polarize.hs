-- This module "polarizes" a neutral term into a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value. A detailed explanation of Call-By-Push-Value can be found
-- in P. Levy, "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis,
-- Queen Mary College, 2001.
module Polarize
  ( polarize
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.List
import Prelude hiding (pi)

import Data.Basic
import Data.Code
import Data.Env
import Data.Term
import Reduce.Term

import qualified Text.Show.Pretty as Pr

polarize :: TermPlus -> WithEnv CodePlus
polarize (m, TermTau) = do
  let ml = snd $ obtainInfoMeta m
  v <- cartesianUniv ml
  return (ml, CodeUpIntro v)
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataUpsilon x))
polarize (m, TermPi _ _) = do
  let ml = snd $ obtainInfoMeta m
  returnClosureType ml
polarize (m, TermPiIntro xts e) = do
  let xs = map fst xts
  let fvs = obtainFreeVarList xs e
  e' <- polarize e
  makeClosure Nothing fvs m xts e'
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  callClosure m e' es
polarize (m, TermMu (f, t) e) = do
  let ml = snd $ obtainInfoMeta m
  let (nameList, _, typeList) = unzip3 $ obtainFreeVarList [f] e
  let fvs = zip nameList typeList
  let fvs' = map toTermUpsilon fvs
  let clsMuType = (MetaTerminal ml, TermPi fvs t)
  let lamBody =
        substTermPlus
          [ ( f
            , ( MetaNonTerminal t ml
              , TermPiElim (MetaNonTerminal clsMuType ml, TermTheta f) fvs'))
          ]
          e
  let clsMeta = MetaNonTerminal clsMuType ml
  lamBody' <- polarize lamBody
  -- ここはクロージャではなく直接呼び出すように最適化が可能
  -- (その場合は上のsubstTermPlusの中のTermPiElimを「直接の」callへと書き換える必要がある)
  -- いや、clsにすぐcallClosureしてるから、インライン展開で結局直接の呼び出しになるのでは？
  cls <- makeClosure (Just f) [] clsMeta fvs lamBody'
  callClosure m cls fvs'
polarize (m, TermIntS size l) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataIntS size l))
polarize (m, TermIntU size l) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataIntU size l))
polarize (m, TermFloat16 l) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataFloat16 l))
polarize (m, TermFloat32 l) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataFloat32 l))
polarize (m, TermFloat64 l) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataFloat64 l))
polarize (m, TermEnum _) = do
  let ml = snd $ obtainInfoMeta m
  v <- cartesianImmediate ml
  return (ml, CodeUpIntro v)
polarize (m, TermEnumIntro l) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataEnumIntro l))
polarize (m, TermEnumElim e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (yName, e', y) <- polarize' e
  let ml = snd $ obtainInfoMeta m
  return $ bindLet [(yName, e')] (ml, CodeEnumElim y (zip cs es'))
polarize (m, TermArray _ _) = do
  let ml = snd $ obtainInfoMeta m
  returnArrayType ml
polarize (m, TermArrayIntro k les) = do
  let ml = snd $ obtainInfoMeta m
  v <- cartesianImmediate ml
  let retKindType = (ml, CodeUpIntro v)
  -- arrayType = Sigma [_ : IMMEDIATE, ..., _ : IMMEDIATE]
  name <- newNameWith "array"
  arrayType <-
    cartesianSigma name ml $ map Left $ replicate (length les) retKindType
  let (ls, es) = unzip les
  (zs, es', xs) <- unzip3 <$> mapM polarize' es
  return $
    bindLet (zip zs es') $
    ( ml
    , CodeUpIntro $
      (ml, DataSigmaIntro [arrayType, (ml, DataArrayIntro k (zip ls xs))]))
polarize (m, TermArrayElim k e1 e2) = do
  let ml = snd $ obtainInfoMeta m
  e1' <- polarize e1
  e2' <- polarize e2
  (arrVarName, arrVar) <- newDataUpsilonWith "arr"
  (idxVarName, idxVar) <- newDataUpsilonWith "idx"
  affVarName <- newNameWith "aff"
  relVarName <- newNameWith "rel"
  (contentTypeVarName, contentTypeVar) <- newDataUpsilonWith "array-type"
  (contentVarName, contentVar) <- newDataUpsilonWith "array-content"
  retUnivType <- returnCartesianUniv
  retImmType <- returnCartesianImmediate
  let retContentType = (ml, CodeUpIntro contentTypeVar)
  -- array : Sigma [content-type : univ, content : content-type]
  return $
    bindLet [(arrVarName, e1'), (idxVarName, e2')] $
    ( ml
    , CodeSigmaElim
        [(contentTypeVarName, retUnivType), (contentVarName, retContentType)]
        arrVar
        ( ml
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            contentTypeVar
            (ml, CodeArrayElim k contentVar idxVar)))

obtainFreeVarList ::
     [Identifier] -> TermPlus -> [(Identifier, Maybe Loc, TermPlus)]
obtainFreeVarList xs e = do
  filter (\(x, _, _) -> x `notElem` xs) $ varTermPlus e

polarize' :: TermPlus -> WithEnv (Identifier, CodePlus, DataPlus)
polarize' e@(m, _) = do
  e' <- polarize e
  (varName, var) <- newDataUpsilonWith' "var" $ snd $ obtainInfoMeta m
  return (varName, e', var)

makeClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, Maybe Loc, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e`
  -> Meta -- meta of lambda
  -> [(Identifier, TermPlus)] -- the `(x1 : A1, ..., xn : An)` in `lam (x1 : A1, ..., xn : An). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
makeClosure mName fvs m xts e = do
  let (xs, _) = unzip xts
  let ml = snd $ obtainInfoMeta m
  let (freeVarNameList, locList, freeVarTypeList) = unzip3 fvs
  negTypeList <- mapM polarize freeVarTypeList
  expName <- newNameWith "exp"
  envExp <- cartesianSigma expName ml $ map Left negTypeList
  (envVarName, envVar) <- newDataUpsilonWith "env"
  let (xs', ts) = unzip $ zip freeVarNameList freeVarTypeList ++ xts
  ts' <- mapM polarize ts
  e' <- linearize (zip xs' ts') e
  let fvInfo = zip freeVarNameList negTypeList
  -- let body = (ml, CodeSigmaElim freeVarNameList envVar e')
  let body = (ml, CodeSigmaElim fvInfo envVar e')
  let fvSigmaIntro =
        ( ml
        , DataSigmaIntro $ zipWith (curry toDataUpsilon) freeVarNameList locList)
  name <-
    case mName of
      Just lamThetaName -> return lamThetaName
      Nothing -> newNameWith "thunk"
  cenv <- gets codeEnv
  when (name `notElem` map fst cenv) $ insCodeEnv name (envVarName : xs) body
  return $
    ( ml
    , CodeUpIntro
        (ml, DataSigmaIntro [envExp, fvSigmaIntro, (ml, DataTheta name)]))

callClosure :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure m e es = do
  (zs, es', xs) <- unzip3 <$> mapM polarize' es
  let ml = snd $ obtainInfoMeta m
  (clsVarName, clsVar) <- newDataUpsilonWith "closure"
  (typeVarName, typeVar) <- newDataUpsilonWith "exp"
  (envVarName, envVar) <- newDataUpsilonWith "env"
  (lamVarName, lamVar) <- newDataUpsilonWith "thunk"
  affVarName <- newNameWith "aff"
  relVarName <- newNameWith "rel"
  retUnivType <- returnCartesianUniv
  retImmType <- returnCartesianImmediate
  return $
    bindLet
      ((clsVarName, e) : zip zs es')
      ( ml
      , CodeSigmaElim
          [ (typeVarName, retUnivType)
          , (envVarName, returnUpsilon typeVarName)
          , (lamVarName, retImmType)
          ]
          clsVar
          ( ml
          , CodeSigmaElim
              [(affVarName, retImmType), (relVarName, retImmType)]
              typeVar
              (ml, CodePiElimDownElim lamVar (envVar : xs))))

-- e' <- linearize xts eのとき、e'は、eとbeta-equivalentであり、かつ、xtsに含まれる変数の使用がpractically linearであるようなterm.
linearize :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
linearize xts (m, CodeSigmaElim yts d e) = do
  let xts' = filter (\(x, _) -> x `elem` varCode e) xts
  -- xts'は、xtsのうち実際にeで使用されている変数の集合。実際に使用されているのでeのなかでcopyが起こりうる。
  -- eのなかで使用されていないものを放置するのは、それらはなるべく早くfreeしたほうが空間的に効率的だから。
  -- copyは遅ければ遅いほど効率的だし、freeは早ければ早いほど効率的。
  -- なお、sigmaの型はすべてclosedなので、ytsのなかに変な自由変数が現れたりすることはない。
  -- つまり、yts = [(y1, ret t1), ..., (yn, ret tn)]とおくと、Sigma (y1 : t1, ..., yn : tn)は
  -- closedなsigmaになっている。
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
  let ml = Nothing
  return (ml, CodeUpElim z (ml, CodeUpIntro (ml, DataUpsilon x)) e')
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
  discardUnusedVar <- toAffineApp Nothing x t
  return (Nothing, CodeUpElim hole discardUnusedVar e)

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
  let ml = fst cont
  cont' <- withHeaderRelevant' t relVar chain cont
  (sigVarName, sigVar) <- newDataUpsilonWith "sig"
  let varX = toDataUpsilon (x, Nothing)
  return $
    ( ml
    , CodeUpElim
        sigVarName
        (ml, CodePiElimDownElim relVar [varX])
        (ml, CodeSigmaElim [(x1, t), (x2, t)] sigVar cont'))

bindLet :: [(Identifier, CodePlus)] -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = do
  let cont' = bindLet xes cont
  (fst cont', CodeUpElim x e cont')

returnUpsilon :: Identifier -> CodePlus
returnUpsilon x = (Nothing, CodeUpIntro (Nothing, DataUpsilon x))

returnArrayType :: Maybe Loc -> WithEnv CodePlus
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

returnClosureType :: Maybe Loc -> WithEnv CodePlus
returnClosureType ml = do
  imm <- cartesianImmediate ml
  tau <- cartesianUniv ml
  (envVarName, envVar) <- newDataUpsilonWith "env"
  let retUnivType = (ml, CodeUpIntro tau)
  let retImmType = (ml, CodeUpIntro imm)
  let retEnvVar = (ml, CodeUpIntro envVar)
  closureType <-
    cartesianSigma
      "closure"
      ml
      [Right (envVarName, retUnivType), Left retEnvVar, Left retImmType]
  return (ml, CodeUpIntro closureType)

returnCartesianImmediate :: WithEnv CodePlus
returnCartesianImmediate = do
  v <- cartesianImmediate Nothing
  return (Nothing, CodeUpIntro v)

cartesianImmediate :: Maybe Loc -> WithEnv DataPlus
cartesianImmediate ml = do
  aff <- affineImmediate ml
  rel <- relevantImmediate ml
  return (ml, DataSigmaIntro [aff, rel])

affineImmediate :: Maybe Loc -> WithEnv DataPlus
affineImmediate ml = do
  cenv <- gets codeEnv
  let thetaName = "affine-immediate"
  let theta = (ml, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      immVarName <- newNameWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        (Nothing, CodeUpIntro (Nothing, DataSigmaIntro []))
      return theta

relevantImmediate :: Maybe Loc -> WithEnv DataPlus
relevantImmediate ml = do
  cenv <- gets codeEnv
  let thetaName = "relevant-immediate"
  let theta = (ml, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      (immVarName, immVar) <- newDataUpsilonWith "arg"
      insCodeEnv
        thetaName
        [immVarName]
        (Nothing, CodeUpIntro (Nothing, DataSigmaIntro [immVar, immVar]))
      return theta

returnCartesianUniv :: WithEnv CodePlus
returnCartesianUniv = do
  v <- cartesianUniv Nothing
  return (Nothing, CodeUpIntro v)

cartesianUniv :: Maybe Loc -> WithEnv DataPlus
cartesianUniv ml = do
  aff <- affineUniv ml
  rel <- relevantUniv ml
  return (ml, DataSigmaIntro [aff, rel])

-- \x -> let (_, _) := x in unit
affineUniv :: Maybe Loc -> WithEnv DataPlus
affineUniv ml = do
  cenv <- gets codeEnv
  let thetaName = "affine-univ"
  let theta = (ml, DataTheta thetaName)
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
        ( Nothing
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            (Nothing, CodeUpIntro (Nothing, DataSigmaIntro [])))
      return theta

relevantUniv :: Maybe Loc -> WithEnv DataPlus
relevantUniv ml = do
  cenv <- gets codeEnv
  let thetaName = "relevant-univ"
  let theta = (ml, DataTheta thetaName)
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
        ( Nothing
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            univVar
            ( Nothing
            , CodeUpIntro
                ( Nothing
                , DataSigmaIntro
                    [ (Nothing, DataSigmaIntro [affVar, relVar])
                    , (Nothing, DataSigmaIntro [affVar, relVar])
                    ])))
      return theta

cartesianSigma ::
     Identifier
  -> Maybe Loc
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
cartesianSigma thetaName ml mxts = do
  aff <- affineSigma ("affine-" ++ thetaName) ml mxts
  rel <- relevantSigma ("relevant-" ++ thetaName) ml mxts
  return (ml, DataSigmaIntro [aff, rel])

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
  -> Maybe Loc
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
affineSigma thetaName ml mxts = do
  cenv <- gets codeEnv
  let theta = (ml, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      xts <- mapM supplyName mxts
      (z, varZ) <- newDataUpsilonWith "arg"
      -- As == [APP-1, ..., APP-n]   (`a` here stands for `app`)
      as <- forM xts $ \(x, e) -> toAffineApp ml x e
      ys <- mapM (const $ newNameWith "arg") xts
      -- yts <- mapM (newNameWithType . snd) xts
      -- let body = bindLet (zip yts as) (ml, CodeUpIntro (ml, DataSigmaIntro []))
      let body = bindLet (zip ys as) (ml, CodeUpIntro (ml, DataSigmaIntro []))
      body' <- linearize xts body
      insCodeEnv thetaName [z] (ml, CodeSigmaElim xts varZ body')
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
  -> Maybe Loc
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
relevantSigma thetaName ml mxts = do
  cenv <- gets codeEnv
  let theta = (ml, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return theta
    Nothing -> do
      xts <- mapM supplyName mxts
      (z, varZ) <- newDataUpsilonWith "arg"
      -- as == [APP-1, ..., APP-n]
      as <- forM xts $ \(x, e) -> toRelevantApp ml x e
      -- pairVarNameList == [pair-1, ...,  pair-n]
      (pairVarNameList, pairVarTypeList) <- unzip <$> mapM toPairInfo xts
      transposedPair <- transposeSigma pairVarTypeList
      let body = bindLet (zip pairVarNameList as) transposedPair
      body' <- linearize xts body
      insCodeEnv thetaName [z] (ml, CodeSigmaElim xts varZ body')
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
    ( Nothing
    , CodeUpIntro
        ( Nothing
        , DataSigmaIntro
            [ (Nothing, DataSigmaIntro xVarList)
            , (Nothing, DataSigmaIntro yVarList)
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
toAffineApp :: Maybe Loc -> Identifier -> CodePlus -> WithEnv CodePlus
toAffineApp ml x e = do
  (expVarName, expVar) <- newDataUpsilonWith "exp"
  (affVarName, affVar) <- newDataUpsilonWith "aff"
  (relVarName, _) <- newDataUpsilonWith "rel"
  retImmType <- returnCartesianImmediate
  return
    ( ml
    , CodeUpElim
        expVarName
        e
        ( Just (111, 222)
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (ml, CodePiElimDownElim affVar [toDataUpsilon (x, fst e)])))

-- toRelevantApp ML x e ~>
--   bind f := e in
--   let (aff, rel) := f in
--   rel @ x
toRelevantApp :: Maybe Loc -> Identifier -> CodePlus -> WithEnv CodePlus
toRelevantApp ml x e = do
  (expVarName, expVar) <- newDataUpsilonWith "rel-app-exp"
  (affVarName, _) <- newDataUpsilonWith "rel-app-aff"
  (relVarName, relVar) <- newDataUpsilonWith "rel-app-rel"
  retImmType <- returnCartesianImmediate
  return
    ( ml
    , CodeUpElim
        expVarName
        e
        ( ml
        , CodeSigmaElim
            [(affVarName, retImmType), (relVarName, retImmType)]
            expVar
            (ml, CodePiElimDownElim relVar [toDataUpsilon (x, fst e)])))

polarizeTheta :: Meta -> Identifier -> WithEnv CodePlus
polarizeTheta m name
  | Just (lowType, op) <- asUnaryOpMaybe name =
    polarizeUnaryOp name op lowType m
polarizeTheta m name
  | Just (lowType, op) <- asBinaryOpMaybe name =
    polarizeBinaryOp name op lowType m
polarizeTheta m name
  | Just (sysCall, len, idxList) <- asSysCallMaybe name =
    polarizeSysCall name sysCall len idxList m
polarizeTheta m name
  | Just _ <- asLowTypeMaybe name = polarize (m, TermEnum $ EnumTypeLabel "top")
polarizeTheta m "is-enum" = polarizeIsEnum m
polarizeTheta m "unsafe.eval-io" = polarizeEvalIO m
polarizeTheta m "file-descriptor" = polarize (m, TermTheta "i64")
polarizeTheta m "stdin" = polarize (m, TermIntS 64 0)
polarizeTheta m "stdout" = polarize (m, TermIntS 64 1)
polarizeTheta m "stderr" = polarize (m, TermIntS 64 2)
polarizeTheta m name = do
  mx <- asEnumConstant name
  case mx of
    Just i -> polarize (m, TermIntS 64 i) -- enum.top ~> 1, enum.choice ~> 2, etc.
    -- muで導入されたthetaに由来するものもここにくる。
    -- たぶんたんにreturn (DataTheta f)とすればよい。
    Nothing -> throwError $ "polarize.theta: " ++ name

-- {enum.top, enum.choice, etc.} ~> {(the number of contents in enum)}
asEnumConstant :: Identifier -> WithEnv (Maybe Integer)
asEnumConstant x
  | ["enum", y] <- wordsBy '.' x = do
    eenv <- gets enumEnv
    case lookup y eenv of
      Nothing -> return Nothing
      Just ls -> return $ Just $ toInteger $ length ls
asEnumConstant _ = return Nothing

polarizeUnaryOp :: Identifier -> UnaryOp -> LowType -> Meta -> WithEnv CodePlus
polarizeUnaryOp name op lowType m = do
  let (t, ml) = obtainInfoMeta m
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [(x, tx)] _) -> do
      let varX = toDataUpsilon (x, Nothing)
      makeClosure
        (Just name)
        []
        m
        [(x, tx)]
        (ml, CodeTheta (ThetaUnaryOp op lowType varX))
    _ -> throwError $ "the arity of " ++ name ++ " is wrongi"

polarizeBinaryOp ::
     Identifier -> BinaryOp -> LowType -> Meta -> WithEnv CodePlus
polarizeBinaryOp name op lowType m = do
  let (t, ml) = obtainInfoMeta m
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [(x, tx), (y, ty)] _) -> do
      let varX = toDataUpsilon (x, Nothing)
      let varY = toDataUpsilon (y, Nothing)
      makeClosure
        (Just name)
        []
        m
        [(x, tx), (y, ty)]
        (ml, CodeTheta (ThetaBinaryOp op lowType varX varY))
    _ -> throwError $ "the arity of " ++ name ++ " is wrongi"

polarizeIsEnum :: Meta -> WithEnv CodePlus
polarizeIsEnum m = do
  let (t, ml) = obtainInfoMeta m
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [(x, tx)] _) -> do
      v <- cartesianImmediate ml
      let varX = toDataUpsilon (x, Nothing)
      aff <- newNameWith "aff"
      rel <- newNameWith "rel"
      retImmType <- returnCartesianImmediate
      makeClosure
        (Just "is-enum")
        []
        m
        [(x, tx)]
        ( ml
        , CodeSigmaElim
            [(aff, retImmType), (rel, retImmType)]
            varX
            (ml, CodeUpIntro v))
    _ -> throwError $ "the type of is-enum is wrong. t :\n" ++ Pr.ppShow t

--    unsafe.eval-io
-- ~> lam x.
--      bind sig := call-closure(x, [0]) in
--      let (resultEnv, value) := sig in
--      return value
--    (as closure)
polarizeEvalIO :: Meta -> WithEnv CodePlus
polarizeEvalIO m = do
  let (t, ml) = obtainInfoMeta m
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi [arg] _) -> do
      (resultValue, resultValueVar) <- newDataUpsilonWith "result"
      (sig, sigVar) <- newDataUpsilonWith "eval-io-sig"
      resultEnv <- newNameWith "env"
      arg' <- polarize $ toTermUpsilon arg
      -- IO Top == Top -> (Bottom, Top)
      evalArgWithZero <- callClosure m arg' [toTermInt64 0]
      retImmType <- returnCartesianImmediate
      makeClosure
        (Just "unsafe.eval-io")
        []
        m
        [arg]
        ( ml
        , CodeUpElim
            sig
            evalArgWithZero
            ( ml
            , CodeSigmaElim
                -- Since `resultEnv` is evaluated into 0,
                -- we can set resultEnv : retImmType (despite the fact that its actual type is bottom).
                [(resultEnv, retImmType), (resultValue, retImmType)] -- (Bottom, Top)
                sigVar
                (ml, CodeUpIntro resultValueVar)))
    _ -> throwError "the type of unsafe.eval-io is wrong"

-- インデックス部分についての説明。たとえばsystem callとしてのwriteは、対象言語では
--   unsafe.write : Pi (A : Univ, out : file-descriptor, str : u8-array a, len : is-enum A). top
-- などと宣言されることになる。他方で実際のsystem callの引数は
--   write(FILE_DESCRIPTOR, STRING_BUFFER, LENGTH)
-- という感じなので、unsafe.writeの引数Aの部分が不要である。この不要な部分と必要な部分を指定するためにpolarizeSyscallは
-- 引数としてインデックスの情報をとっている。unsafe.writeの例で言えば、長さについての情報は4であり、"used arguments" を
-- 指定する配列は、zero-indexであることに注意して [1, 2, 3] となる。
polarizeSysCall ::
     Identifier -- the name of theta
  -> SysCall -- the kind of system call
  -> Int -- the length of the arguments of the theta
  -> [Int] -- used (or, non-discarded) arguments in its actual implementation (index starts from zero)
  -> Meta -- the meta of the theta
  -> WithEnv CodePlus
polarizeSysCall name sysCall argLen argIdxList m = do
  let (t, ml) = obtainInfoMeta m
  t' <- reduceTermPlus t
  case t' of
    (_, TermPi xts _)
      | length xts == argLen -> do
        let ys = map (\i -> toVar $ fst $ xts !! i) argIdxList
        makeClosure
          (Just name)
          []
          m
          xts
          (ml, CodeTheta (ThetaSysCall sysCall ys))
    _ -> throwError $ "the type of " ++ name ++ " is wrong"

toVar :: Identifier -> DataPlus
toVar x = (Nothing, DataUpsilon x)

newDataUpsilonWith :: Identifier -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith name = newDataUpsilonWith' name Nothing

newDataUpsilonWith' :: Identifier -> Maybe Loc -> WithEnv (Identifier, DataPlus)
newDataUpsilonWith' name ml = do
  x <- newNameWith name
  return (x, (ml, DataUpsilon x))

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Right (x, t)) = return (x, t)
supplyName (Left t) = do
  x <- newNameWith "unused-sigarg"
  return (x, t)
