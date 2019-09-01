-- This module "polarizes" a neutral term into a negMetaative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value, although this translation doesn't preserve types when the
-- given term includes dependent sigma-elimination. A detailed explanation of
-- Call-By-Push-Value can be found in P. Levy, "Call-by-Push-Value: A Subsuming
-- Paradigm". Ph. D. thesis, Queen Mary College, 2001.
module Polarize
  ( polarize
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Data.List            (nubBy)
import           Prelude              hiding (pi)

import           Data.Basic
import           Data.Code
import           Data.Env
import           Data.Term

polarize :: TermPlus -> WithEnv CodePlus
polarize (m, TermTau) = do
  (xt, u, ml) <- polarizeMeta m
  bindLet xt (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataImmediate))
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (xt, u, ml) <- polarizeMeta m
  bindLet xt (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataUpsilon x))
polarize (m, TermEpsilon _) = do
  (xt, u, ml) <- polarizeMeta m
  bindLet xt (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataImmediate))
polarize (m, TermEpsilonIntro l) = do
  (xt, u, ml) <- polarizeMeta m
  bindLet
    xt
    (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataEpsilonIntro l))
polarize (m, TermEpsilonElim (x, t) e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (yts, y) <- polarize' e
  (zts, z) <- polarize' t
  (xt, tm, ml) <- polarizeMeta m
  bindLet
    (xt ++ yts ++ zts)
    (negMeta (up tm ml) ml, CodeEpsilonElim (x, z) y (zip cs es'))
polarize (m, TermPi _ _) = do
  let ml = snd $ obtainInfoMeta m
  envVarName <- newNameWith "gamma"
  let envVar = (DataMetaTerminal ml, DataUpsilon envVarName)
  tmp1 <- newNameWith "tmp"
  tmp2 <- newNameWith "tmp"
  return
    ( undefined
    , CodeUpIntro
        ( DataMetaTerminal ml
        , DataSigma
            [ (envVarName, (DataMetaTerminal ml, DataImmediate))
            , (tmp1, envVar)
            , (tmp2, (DataMetaTerminal ml, DataImmediate))
            ]))
polarize (m, TermPiIntro xts e) = do
  e' <- polarize e
  lamName <- newNameWith "theta"
  makeClosure lamName m xts e'
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  callClosure m e' es
polarize (m, TermMu (f, t) e) = do
  let ml = snd $ obtainInfoMeta m
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  let vs' = map toTermVar vs
  let clsMuType = (MetaTerminal ml, TermPi vs t)
  let lamBody =
        substTermPlus
          [ ( f
            , ( MetaNonTerminal t ml
              , TermPiElim (MetaNonTerminal clsMuType ml, TermTheta f) vs'))
          ]
          e
  lamBody' <- polarize lamBody
  let clsMeta = MetaNonTerminal clsMuType ml
  cls <- makeClosure f clsMeta vs lamBody'
  callClosure m cls vs'

type Binder = [(Identifier, CodePlus)]

polarize' :: TermPlus -> WithEnv (Binder, DataPlus)
polarize' e@(m, _) = do
  e' <- polarize e
  x <- newNameWith "arg"
  case m of
    MetaTerminal ml -> return ([(x, e')], (DataMetaTerminal ml, DataUpsilon x))
    MetaNonTerminal t ml -> do
      (yts, y) <- polarize' t
      return (yts ++ [(x, e')], (DataMetaNonTerminal y ml, DataUpsilon x))

polarizeMeta :: Meta -> WithEnv (Binder, DataPlus, Maybe (Int, Int))
polarizeMeta m = do
  let (t, ml) = obtainInfoMeta m
  (binder, d) <- polarize' t
  return (binder, d, ml)

makeClosure ::
     Identifier
  -> Meta
  -> [(Identifier, TermPlus)]
  -> CodePlus
  -> WithEnv CodePlus
makeClosure lamThetaName m xts e = do
  let xps = undefined xts
  let ml = snd $ obtainInfoMeta m
  -- (xt, downPiType, ml) <- polarizeMeta m
  let fvs = nubBy (\x y -> fst x == fst y) $ varCodePlus e
  -- envType = (C1, ..., Cn), where Ci is the types of the free variables in e'
  envType <- toSigmaType ml $ map (Left . snd) fvs
  (envVarName, envVar) <- newVarOfType envType
  let lamBody = (negMeta undefined ml, CodeSigmaElim fvs envVar e)
  -- ((A1, ..., An) -> ↑B) ~> ((ENV, A1, ..., An) -> ↑B)
  -- downPiType' = ↓((ENV, A1, ..., An) -> ↑B)
  -- downPiType' <- toDownPiType ml (Left envType : map Right xpsPi) codType
  let downPiType' = (DataMetaTerminal ml, DataImmediate)
  let lamTheta = (posMeta downPiType' ml, DataTheta lamThetaName)
  -- lamThetaName ~> thunk (lam (envVarName, x1, ..., xn) lamBody)
  penv <- gets polEnv
  when (lamThetaName `elem` map fst penv) $
    insPolEnv lamThetaName ((envVarName, envType) : xps) lamBody
  let fvSigmaIntro = (posMeta envType ml, DataSigmaIntro $ map toVar fvs)
  (typeVarName, typeVar) <- newVarOfType (DataMetaTerminal ml, DataImmediate)
  -- piType'  : ↓(((C1, ..., Cn), A) -> ↑B)
  -- piType'' : ↓((typeVar, A) -> ↑B)
  -- i.e. piType' = piType'' {typeVar := (C1, ..., Cn)}
  -- downPiType'' <- toDownPiType ml (Left typeVar : map Right xpsPi) codType
  -- clsType = Sigma (typeVar : U). (↓((typeVar, A) -> ↑B), typeVar)
  clsType <-
    toSigmaType
      ml
      [ Right (typeVarName, (DataMetaTerminal ml, DataImmediate))
      , Left typeVar
      , Left downPiType'
      ]
  return
    ( negMeta (up clsType ml) ml
    , CodeUpIntro
        (posMeta clsType ml, DataSigmaIntro [envType, fvSigmaIntro, lamTheta]))

callClosure :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure m e@(funMeta, _) es = do
  (ut, u, ml) <- polarizeMeta m
  (xess, xs) <- unzip <$> mapM polarize' es
  (typeVarName, typeVar) <- newVarOfType (DataMetaTerminal ml, DataImmediate)
  let mlPi = snd $ obtainInfoCodeMeta funMeta
  let downPiType = (DataMetaTerminal mlPi, DataImmediate)
  clsType <-
    toSigmaType
      ml
      [ Right (typeVarName, (DataMetaTerminal mlPi, DataImmediate))
      , Left downPiType
      , Left typeVar
      ]
  (clsVarName, clsVar) <- newVarOfType clsType
  (lamVarName, lamVar) <- newVarOfType downPiType
  (envVarName, envVar) <- newVarOfType typeVar
  cont <-
    bindLet
      (ut ++ concat xess)
      ( negMeta (up u ml) ml
      , CodeSigmaElim
          [ (typeVarName, (DataMetaTerminal mlPi, DataImmediate))
          , (envVarName, typeVar)
          , (lamVarName, downPiType)
          ]
          clsVar
          (negMeta (up u ml) ml, CodePiElimDownElim lamVar (envVar : xs)))
  return (negMeta (up u ml) ml, CodeUpElim (clsVarName, clsType) e cont)

toSigmaType ::
     Maybe (Int, Int)
  -> [Either DataPlus (Identifier, DataPlus)]
  -> WithEnv DataPlus
toSigmaType ml xps = do
  xps' <- mapM supplyName xps
  return (DataMetaTerminal ml, DataSigma xps')

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Left t) = do
  x <- newNameWith "hole"
  return (x, t)
supplyName (Right (x, t)) = return (x, t)

toVar :: (Identifier, DataPlus) -> DataPlus
toVar (x, t) = do
  let (_, ml) = obtainInfoDataMeta $ fst t
  (DataMetaNonTerminal t ml, DataUpsilon x)

toTermVar :: (Identifier, TermPlus) -> TermPlus
toTermVar (x, t) = do
  let (_, ml) = obtainInfoMeta $ fst t
  (MetaNonTerminal t ml, TermUpsilon x)

bindLet :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
bindLet [] cont = return cont
bindLet ((x, e):xes) cont = do
  e' <- bindLet xes cont
  let (typeOfCont, ml) = obtainInfoCodeMeta $ fst e'
  let (n, ml) = obtainInfoCodeMeta $ fst e
  y <- newNameWith "var"
  let yVar = (DataMetaTerminal ml, DataUpsilon y)
  let tau = (DataMetaTerminal ml, DataImmediate)
  -- kleisli extension (i.e. dependent up-elimination)
  let ke =
        ( fst typeOfCont
        , CodeUpElim
            (y, tau)
            n
            (fst typeOfCont, CodeUpElim (x, yVar) e typeOfCont))
  return
    ( negMeta ke ml
    , CodeUpElim (y, tau) n (negMeta ke ml, CodeUpElim (x, yVar) e e'))

posMeta :: DataPlus -> Maybe (Int, Int) -> DataMeta
posMeta = DataMetaNonTerminal

negMeta :: CodePlus -> Maybe (Int, Int) -> CodeMeta
negMeta = CodeMetaNonTerminal

up :: DataPlus -> Maybe (Int, Int) -> CodePlus
up u ml = (CodeMetaTerminal ml, CodeUp u)

-- expand definitions of constants
-- polarizeTheta :: Meta -> Identifier -> WithEnv CodePlus
-- polarizeTheta m name@"core.i8.add"    = polarizeThetaArith name ArithAdd m
-- polarizeTheta m name@"core.i16.add"   = polarizeThetaArith name ArithAdd m
-- polarizeTheta m name@"core.i32.add"   = polarizeThetaArith name ArithAdd m
-- polarizeTheta m name@"core.i64.add"   = polarizeThetaArith name ArithAdd m
-- polarizeTheta m name@"core.i8.sub"    = polarizeThetaArith name ArithSub m
-- polarizeTheta m name@"core.i16.sub"   = polarizeThetaArith name ArithSub m
-- polarizeTheta m name@"core.i32.sub"   = polarizeThetaArith name ArithSub m
-- polarizeTheta m name@"core.i64.sub"   = polarizeThetaArith name ArithSub m
-- polarizeTheta m name@"core.i8.mul"    = polarizeThetaArith name ArithMul m
-- polarizeTheta m name@"core.i16.mul"   = polarizeThetaArith name ArithMul m
-- polarizeTheta m name@"core.i32.mul"   = polarizeThetaArith name ArithMul m
-- polarizeTheta m name@"core.i64.mul"   = polarizeThetaArith name ArithMul m
-- polarizeTheta m name@"core.i8.div"    = polarizeThetaArith name ArithDiv m
-- polarizeTheta m name@"core.i16.div"   = polarizeThetaArith name ArithDiv m
-- polarizeTheta m name@"core.i32.div"   = polarizeThetaArith name ArithDiv m
-- polarizeTheta m name@"core.i64.div"   = polarizeThetaArith name ArithDiv m
-- polarizeTheta m name@"core.f32.add"   = polarizeThetaArith name ArithAdd m
-- polarizeTheta m name@"core.f64.add"   = polarizeThetaArith name ArithAdd m
-- polarizeTheta m name@"core.f32.sub"   = polarizeThetaArith name ArithSub m
-- polarizeTheta m name@"core.f64.sub"   = polarizeThetaArith name ArithSub m
-- polarizeTheta m name@"core.f32.mul"   = polarizeThetaArith name ArithMul m
-- polarizeTheta m name@"core.f64.mul"   = polarizeThetaArith name ArithMul m
-- polarizeTheta m name@"core.f32.div"   = polarizeThetaArith name ArithDiv m
-- polarizeTheta m name@"core.f64.div"   = polarizeThetaArith name ArithDiv m
-- polarizeTheta m name@"core.print.i64" = polarizeThetaPrint name m
-- polarizeTheta _ _                     = throwError "polarize.theta"
-- polarizeThetaArith :: Identifier -> Arith -> Meta -> WithEnv CodePlus
-- polarizeThetaArith name op m = do
--   (xt, upT, ml) <- polarizeMeta m
--   case upT of
--     (_, DataDownPi _ (_, CodeUp numType)) -> do
--       (x, varX) <- newVarOfType numType
--       (y, varY) <- newVarOfType numType
--       makeClosure
--         name
--         m
--         [(x, undefined), (y, undefined)]
--         (negMeta (up numType ml) ml, CodeTheta (ThetaArith op varX varY))
--     _ -> throwError "polarize.theta.arith"
-- polarizeThetaPrint :: Identifier -> Meta -> WithEnv CodePlus
-- polarizeThetaPrint name m = do
--   (xt, upT, ml) <- polarizeMeta m
--   case upT of
--     (_, DataDownPi [(_, int)] cod) -> do
--       (x, varX) <- newVarOfType int
--       makeClosure
--         name
--         m
--         [(x, undefined)]
--         (negMeta cod ml, CodeTheta (ThetaPrint varX))
--     _ -> throwError "polarize.theta.print"
newVarOfType :: DataPlus -> WithEnv (Identifier, DataPlus)
newVarOfType t = do
  x <- newNameWith "arg"
  return (x, (posMeta t Nothing, DataUpsilon x))

-- -- This module "polarizes" a neutral term into a negative term. Operationally,
-- -- this corresponds to determination of the order of evaluation. In proof-theoretic
-- -- term, we translate a ordinary dependent calculus to a dependent variant of
-- -- Call-By-Push-Value. A detailed explanation of Call-By-Push-Value can be found
-- -- in P. Levy, "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis,
-- -- Queen Mary College, 2001.
-- --
-- -- Every type is converted into an "exponent", which is a function that receives
-- -- an integer `n` and a term `e` of that type, and returns n-copy of `e`, namely,
-- -- returns (e, ..., e). This operation roughly corresponds to eta-expansion. Indeed,
-- -- when the integer `n` equals to 1, this exponential operation degenerates to
-- -- eta-expansion.
-- module Polarize
--   ( polarize
--   ) where
-- import           Control.Monad.Except
-- import           Control.Monad.State
-- import           Data.List            (nubBy)
-- import           Prelude              hiding (pi)
-- import           Data.Basic
-- import           Data.Code
-- import           Data.Env
-- import           Data.Term
-- import           Reduce.Term
-- polarize :: TermPlus -> WithEnv CodePlus
-- polarize (m, TermTau) = do
--   i <- exponentImmediate
--   return (snd $ obtainInfoMeta m, CodeUpIntro i)
-- polarize (m, TermTheta x) = polarizeTheta m x
-- polarize (m, TermUpsilon x) = do
--   let ml = snd $ obtainInfoMeta m
--   return (ml, CodeUpIntro (ml, DataUpsilon x))
-- polarize (m, TermEpsilon _) = do
--   i <- exponentImmediate
--   return (snd $ obtainInfoMeta m, CodeUpIntro i)
-- polarize (m, TermEpsilonIntro l) = do
--   let (t, ml) = obtainInfoMeta m
--   t' <- reduceTermPlus t
--   case t' of
--     (_, TermEpsilon i)
--       | Just lowType <- asLowType i ->
--         return (ml, CodeUpIntro (ml, DataEpsilonIntro l lowType))
--     _ -> undefined
-- polarize (m, TermEpsilonElim (x, t) e bs) = do
--   let (cs, es) = unzip bs
--   es' <- mapM polarize es
--   (yts, y) <- polarize' e
--   (zts, z) <- polarize' t
--   let ml = snd $ obtainInfoMeta m
--   return $ bindLet (yts ++ zts) (ml, CodeEpsilonElim (x, z) y (zip cs es'))
-- polarize (m, TermPi _ _) = do
--   let ml = snd $ obtainInfoMeta m
--   clsExp <- exponentClosure
--   return (ml, CodeUpIntro clsExp)
-- polarize (m, TermPiIntro xts e) = do
--   lamName <- newNameWith "theta"
--   makeClosure lamName m (map fst xts) e
-- polarize (m, TermPiElim e es) = do
--   e' <- polarize e
--   callClosure m e' es
-- polarize (m, TermMu (f, t) e) = do
--   let ml = snd $ obtainInfoMeta m
--   let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
--   let vs' = map toTermUpsilon vs
--   let clsMuType = (MetaTerminal ml, TermPi vs t)
--   let lamBody =
--         substTermPlus
--           [ ( f
--             , ( MetaNonTerminal t ml
--               , TermPiElim (MetaNonTerminal clsMuType ml, TermTheta f) vs'))
--           ]
--           e
--   let clsMeta = MetaNonTerminal clsMuType ml
--   cls <- makeClosure f clsMeta (map fst vs) lamBody
--   callClosure m cls vs'
-- type Binder = [(Identifier, CodePlus)]
-- polarize' :: TermPlus -> WithEnv (Binder, DataPlus)
-- polarize' e@(m, _) = do
--   e' <- polarize e
--   (varName, var) <- newDataUpsilon' $ snd $ obtainInfoMeta m
--   return ([(varName, e')], var)
-- makeClosure ::
--      Identifier -> Meta -> [Identifier] -> TermPlus -> WithEnv CodePlus
-- makeClosure lamThetaName m xs e = do
--   let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
--   let fvs = filter (\(x, _) -> x `notElem` xs) vs
--   e' <- polarize e
--   makeClosure' fvs lamThetaName m xs e'
-- makeClosure' ::
--      [(Identifier, TermPlus)]
--   -> Identifier
--   -> Meta
--   -> [Identifier]
--   -> CodePlus
--   -> WithEnv CodePlus
-- makeClosure' fvs lamThetaName m xs e = do
--   let ml = snd $ obtainInfoMeta m
--   let (freeVarNameList, freeVarTypeList) = unzip fvs
--   (yess, ys) <- unzip <$> mapM polarize' freeVarTypeList
--   envExpName <- newNameWith "exp"
--   envExp <- exponentSigma envExpName ml $ map Left ys
--   (envVarName, envVar) <- newDataUpsilon
--   let lamBody = (ml, CodeSigmaElim (map fst fvs) envVar e)
--   let lamTheta = (ml, DataTheta lamThetaName)
--   penv <- gets polEnv
--   when (lamThetaName `elem` map fst penv) $
--     insPolEnv lamThetaName (envVarName : xs) lamBody
--   let fvSigmaIntro =
--         ( ml
--         , DataSigmaIntro $
--           zipWith (curry toDataUpsilon) freeVarNameList (map fst ys))
--   return $
--     bindLet
--       (concat yess)
--       (ml, CodeUpIntro (ml, DataSigmaIntro [envExp, fvSigmaIntro, lamTheta]))
-- callClosure :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
-- callClosure m e es = do
--   (xess, xs) <- unzip <$> mapM polarize' es
--   let ml = snd $ obtainInfoMeta m
--   (clsVarName, clsVar) <- newDataUpsilon
--   (typeVarName, _) <- newDataUpsilon
--   (envVarName, envVar) <- newDataUpsilon
--   (lamVarName, lamVar) <- newDataUpsilon
--   return
--     ( ml
--     , CodeUpElim
--         clsVarName
--         e
--         (bindLet
--            (concat xess)
--            ( ml
--            , CodeSigmaElim
--                -- optimizable: ここでのtypevarの取得は省略可能
--                [typeVarName, envVarName, lamVarName]
--                clsVar
--                (ml, CodePiElimDownElim lamVar (envVar : xs)))))
-- bindLet :: Binder -> CodePlus -> CodePlus
-- bindLet [] cont = cont
-- bindLet ((x, e):xes) cont = do
--   let e' = bindLet xes cont
--   (fst e', CodeUpElim x e e')
-- exponentImmediate :: WithEnv DataPlus
-- exponentImmediate = do
--   penv <- gets polEnv
--   let thetaName = "EXPONENT.IMMEDIATE"
--   let immExp = (Nothing, DataTheta thetaName)
--   case lookup thetaName penv of
--     Just _ -> return immExp
--     Nothing -> do
--       (countVarName, countVar) <- newDataUpsilon
--       (immVarName, immVar) <- newDataUpsilon
--       let lamBody = (Nothing, CodeCopyN countVar immVar)
--       insPolEnv thetaName [countVarName, immVarName] lamBody
--       return (Nothing, DataTheta thetaName)
-- -- Sigma (y1 : t1, ..., yn : tn) ~>
-- --   lam (m, z).
-- --     let (y1, ..., yn) := z in
-- --     bind ys1 = t1 @ (m, y1) in
-- --     ...
-- --     bind ysn = tn @ (m, yn) in -- ここまではコードとしてstaticに書ける
-- --     let (ys1-1, ..., ys1-m) := ys1 in -- ここでm-elimが必要になる。
-- --     ...
-- --     let (ysn-1, ..., ysn-m) := ysn in
-- --     ((ys1-1, ..., ysn-1), ..., (ys1-m, ..., ysn-m))
-- --
-- -- (Note that Sigma (y1 : t1, ..., yn : tn) must be closed.)
-- exponentSigma ::
--      Identifier
--   -> Maybe Loc
--   -> [Either DataPlus (Identifier, DataPlus)]
--   -> WithEnv DataPlus
-- exponentSigma lamThetaName ml mxts = do
--   penv <- gets polEnv
--   let sigmaExp = (ml, DataTheta lamThetaName)
--   case lookup lamThetaName penv of
--     Just _ -> return sigmaExp
--     Nothing -> do
--       xts <- mapM supplyName mxts
--       (countVarName, countVar) <- newDataUpsilon
--       (sigVarName, sigVar) <- newDataUpsilon
--       let appList =
--             map
--               (\(x, t) ->
--                  (ml, CodePiElimDownElim t [countVar, toDataUpsilon (x, fst t)]))
--               xts
--       ys <- mapM (const $ newNameWith "var") xts
--       let ys' = map toDataUpsilon' ys
--       let lamBody =
--             ( ml
--             , CodeSigmaElim
--                 (map fst xts)
--                 sigVar
--                 (bindLet (zip ys appList) (ml, CodeTransposeN countVar ys')))
--       insPolEnv lamThetaName [countVarName, sigVarName] lamBody
--       return sigmaExp
-- exponentClosure :: WithEnv DataPlus
-- exponentClosure = do
--   i <- exponentImmediate
--   (typeVarName, typeVar) <- newDataUpsilon
--   exponentSigma
--     "EXPONENT.CLOSURE"
--     Nothing
--     [Right (typeVarName, i), Left typeVar, Left i]
-- supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
-- supplyName (Right (x, t)) = return (x, t)
-- supplyName (Left t) = do
--   x <- newNameWith "hole"
--   return (x, t)
-- -- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv CodePlus
polarizeTheta m name@"core.i8.add" =
  polarizeThetaArith name ArithAdd (LowTypeSignedInt 8) m
polarizeTheta m name@"core.i16.add" =
  polarizeThetaArith name ArithAdd (LowTypeSignedInt 16) m
polarizeTheta m name@"core.i32.add" =
  polarizeThetaArith name ArithAdd (LowTypeSignedInt 32) m
polarizeTheta m name@"core.i64.add" =
  polarizeThetaArith name ArithAdd (LowTypeSignedInt 64) m
polarizeTheta m name@"core.i8.sub" =
  polarizeThetaArith name ArithSub (LowTypeSignedInt 8) m
polarizeTheta m name@"core.i16.sub" =
  polarizeThetaArith name ArithSub (LowTypeSignedInt 16) m
polarizeTheta m name@"core.i32.sub" =
  polarizeThetaArith name ArithSub (LowTypeSignedInt 32) m
polarizeTheta m name@"core.i64.sub" =
  polarizeThetaArith name ArithSub (LowTypeSignedInt 64) m
polarizeTheta m name@"core.i8.mul" =
  polarizeThetaArith name ArithMul (LowTypeSignedInt 8) m
polarizeTheta m name@"core.i16.mul" =
  polarizeThetaArith name ArithMul (LowTypeSignedInt 16) m
polarizeTheta m name@"core.i32.mul" =
  polarizeThetaArith name ArithMul (LowTypeSignedInt 32) m
polarizeTheta m name@"core.i64.mul" =
  polarizeThetaArith name ArithMul (LowTypeSignedInt 64) m
polarizeTheta m name@"core.i8.div" =
  polarizeThetaArith name ArithDiv (LowTypeSignedInt 8) m
polarizeTheta m name@"core.i16.div" =
  polarizeThetaArith name ArithDiv (LowTypeSignedInt 16) m
polarizeTheta m name@"core.i32.div" =
  polarizeThetaArith name ArithDiv (LowTypeSignedInt 32) m
polarizeTheta m name@"core.i64.div" =
  polarizeThetaArith name ArithDiv (LowTypeSignedInt 64) m
polarizeTheta m name@"core.f32.add" =
  polarizeThetaArith name ArithAdd (LowTypeFloat 32) m
polarizeTheta m name@"core.f64.add" =
  polarizeThetaArith name ArithAdd (LowTypeFloat 64) m
polarizeTheta m name@"core.f32.sub" =
  polarizeThetaArith name ArithSub (LowTypeFloat 32) m
polarizeTheta m name@"core.f64.sub" =
  polarizeThetaArith name ArithSub (LowTypeFloat 64) m
polarizeTheta m name@"core.f32.mul" =
  polarizeThetaArith name ArithMul (LowTypeFloat 32) m
polarizeTheta m name@"core.f64.mul" =
  polarizeThetaArith name ArithMul (LowTypeFloat 64) m
polarizeTheta m name@"core.f32.div" =
  polarizeThetaArith name ArithDiv (LowTypeFloat 32) m
polarizeTheta m name@"core.f64.div" =
  polarizeThetaArith name ArithDiv (LowTypeFloat 64) m
polarizeTheta m name@"core.print.i64" = polarizeThetaPrint name m
polarizeTheta _ _ = throwError "polarize.theta"

polarizeThetaArith :: Identifier -> Arith -> LowType -> Meta -> WithEnv CodePlus
polarizeThetaArith name op lowType m = undefined
  -- let ml = snd $ obtainInfoMeta m
  -- (x, varX) <- newDataUpsilon
  -- (y, varY) <- newDataUpsilon
  -- makeClosure'
  --   []
  --   name
  --   m
  --   [x, y]
  --   (ml, CodeTheta (ThetaArith op lowType varX varY))

polarizeThetaPrint :: Identifier -> Meta -> WithEnv CodePlus
polarizeThetaPrint name m = undefined
  -- let ml = snd $ obtainInfoMeta m
  -- (x, varX) <- newDataUpsilon
  -- makeClosure' [] name m [x] (ml, CodeTheta (ThetaPrint varX))
-- newDataUpsilon :: WithEnv (Identifier, DataPlus)
-- newDataUpsilon = newDataUpsilon' Nothing
-- newDataUpsilon' :: Maybe Loc -> WithEnv (Identifier, DataPlus)
-- newDataUpsilon' ml = do
--   x <- newNameWith "arg"
--   return (x, (ml, DataUpsilon x))
-- -- asSignedIntType :: Identifier -> Maybe LowType
-- -- asSignedIntType = undefined
-- -- asFloatType :: Identifier -> Maybe LowType
-- -- asFloatType = undefined
-- asLowType :: Identifier -> Maybe LowType
-- asLowType = undefined
