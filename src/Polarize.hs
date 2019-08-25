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
import           Data.List            (nubBy)
import           Prelude              hiding (pi)

import           Data.Basic
import           Data.Code
import           Data.Env
import           Data.Term
import           Reduce.Code

polarize :: TermPlus -> WithEnv CodePlus
polarize (m, TermTau) = do
  (u, ml) <- polarizeMeta m
  return (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataTau))
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (u, ml) <- polarizeMeta m
  return (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataUpsilon x))
polarize (m, TermEpsilon x) = do
  (u, ml) <- polarizeMeta m
  return (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataEpsilon x))
polarize (m, TermEpsilonIntro l) = do
  (u, ml) <- polarizeMeta m
  return (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataEpsilonIntro l))
polarize (m, TermEpsilonElim (x, t) e bs) = do
  (u, ml) <- polarizeMeta m
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (y, ye) <- polarize' e
  (z, zt) <- polarize' t
  bindLet [ye, zt] (negMeta (up u ml) ml, CodeEpsilonElim (x, z) y (zip cs es'))
polarize (m, TermPi xts t) = do
  (u, ml) <- polarizeMeta m
  p <- polarize t >>= reduceCodePlus >>= extract
  (xs', xts', xs) <- polarizePlus xts
  let negMetaMeta = CodeMetaTerminal ml
  let z' = (negMetaMeta, CodeUp p)
  bindLet
    xts'
    ( negMeta (up u ml) ml
    , CodeUpIntro (posMeta u ml, DataDown (negMetaMeta, CodePi (zip xs xs') z')))
polarize (m, TermPiIntro xts e) = do
  xps <- polarizePlus' xts
  e' <- polarize e
  makeClosure m xps e'
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  es' <- mapM polarize es
  callClosure m e' es'
polarize (m, TermSigma xts) = do
  (u, ml) <- polarizeMeta m
  (ys', yts', xs) <- polarizePlus xts
  bindLet
    yts'
    (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataSigma (zip xs ys')))
polarize (m, TermSigmaIntro es) = do
  (u, ml) <- polarizeMeta m
  (xs, xes) <- unzip <$> mapM polarize' es
  bindLet
    xes
    (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataSigmaIntro xs))
polarize (m, TermSigmaElim xts e1 e2) = do
  (u, ml) <- polarizeMeta m
  (z', ze1') <- polarize' e1
  (ys', yts', xs) <- polarizePlus xts
  e2' <- polarize e2
  bindLet
    (ze1' : yts')
    (negMeta (up u ml) ml, CodeSigmaElim (zip xs ys') z' e2')
polarize (m, TermMu (f, _) e) = do
  (u, ml) <- polarizeMeta m
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  envVar <- newNameWith "env"
  let lamBody =
        ( undefined
        , TermSigmaElim
            vs
            (undefined, TermUpsilon envVar)
            (substTermPlus
               [ ( f
                 , ( undefined
                   , TermPiElim (undefined, TermTheta f) (map undefined vs)))
               ]
               e))
  lamBody' <- polarize lamBody
  cls <- makeClosureWithName f undefined [(envVar, undefined)] lamBody'
  callClosure m cls (map undefined vs)

makeClosure :: Meta -> [(Identifier, DataPlus)] -> CodePlus -> WithEnv CodePlus
makeClosure m xps e = do
  lamName <- newNameWith "theta"
  makeClosureWithName lamName m xps e

makeClosureWithName ::
     Identifier
  -> Meta
  -> [(Identifier, DataPlus)]
  -> CodePlus
  -> WithEnv CodePlus
makeClosureWithName lamThetaName m xps e = do
  (downPiType, ml) <- polarizeMeta m
  let fvs = nubBy (\x y -> fst x == fst y) $ varCodePlus e
  -- envType = (C1, ..., Cn), where Ci is the types of the free variables in e'
  envType <- toSigmaType ml $ map (Left . snd) fvs
  (envVarName, envVar) <- newVarOfType envType
  -- (codType, _) <- polarizeMeta codMeta
  (xpsPi, codType) <- extractFromDownPi downPiType
  let lamBody = (negMeta codType ml, CodeSigmaElim fvs envVar e)
  -- ((A1, ..., An) -> ↑B) ~> ((ENV, A1, ..., An) -> ↑B)
  piType' <- toPiType ml (Left envType : map Right xpsPi) codType
  -- downPiType' = ↓((ENV, A1, ..., An) -> ↑B)
  let downPiType' = down piType' ml
  let lamTheta = (posMeta downPiType' ml, DataTheta lamThetaName)
  -- lamThetaName ~> thunk (lam (envVarName, x1, ..., xn) lamBody)
  insPolEnv lamThetaName ((envVarName, envType) : xps) lamBody
  let fvSigmaIntro = (posMeta envType ml, DataSigmaIntro $ map toVar fvs)
  (typeVarName, typeVar) <- newVarOfType (DataMetaTerminal ml, DataTau)
  -- piType'  : ↓(((C1, ..., Cn), A) -> ↑B)
  -- piType'' : ↓((typeVar, A) -> ↑B)
  -- i.e. piType' = piType'' {typeVar := (C1, ..., Cn)}
  piType'' <- toPiType ml (Left typeVar : map Right xpsPi) codType
  -- clsType = Sigma (typeVar : U). (↓((typeVar, A) -> ↑B), typeVar)
  clsType <-
    toSigmaType
      ml
      [ Right (typeVarName, (DataMetaTerminal ml, DataTau))
      , Left (down piType'' ml)
      , Left typeVar
      ]
  return
    ( negMeta (up clsType ml) ml
    , CodeUpIntro
        (posMeta clsType ml, DataSigmaIntro [envType, lamTheta, fvSigmaIntro]))

callClosure :: Meta -> CodePlus -> [CodePlus] -> WithEnv CodePlus
callClosure m e@(funMeta, _) es = do
  (u, ml) <- polarizeMeta m
  ts <- mapM typeOf es
  (typeVarName, typeVar) <- newVarOfType (DataMetaTerminal ml, DataTau)
  let (upDownPiType, mlPi) = obtainInfoCodeMeta funMeta
  downPiType <- reduceCodePlus upDownPiType >>= extract
  (xpsPi, codType) <- extractFromDownPi downPiType
  piType'' <- toPiType mlPi (Left typeVar : map Right xpsPi) codType
  clsType <-
    toSigmaType
      ml
      [ Right (typeVarName, (DataMetaTerminal mlPi, DataTau))
      , Left (down piType'' mlPi)
      , Left typeVar
      ]
  argList <- mapM newVarOfType ts
  (clsVarName, clsVar) <- newVarOfType clsType
  (lamVarName, lamVar) <- newVarOfType (down piType'' mlPi)
  (envVarName, envVar) <- newVarOfType typeVar
  cont <-
    bindLet
      (zip (map fst argList) es)
      ( negMeta (up u ml) ml
      , CodeSigmaElim
          [ (typeVarName, (DataMetaTerminal mlPi, DataTau))
          , (lamVarName, down piType'' mlPi)
          , (envVarName, typeVar)
          ]
          clsVar
          ( negMeta (up u ml) ml
          , CodePiElimDownElim lamVar (envVar : map toVar argList)))
  return (negMeta (up u ml) ml, CodeUpElim (clsVarName, clsType) e cont)

toSigmaType ::
     Maybe (Int, Int)
  -> [Either DataPlus (Identifier, DataPlus)]
  -> WithEnv DataPlus
toSigmaType ml xps = do
  xps' <- mapM supplyName xps
  return (DataMetaTerminal ml, DataSigma xps')

toPiType ::
     Maybe (Int, Int)
  -> [Either DataPlus (Identifier, DataPlus)]
  -> CodePlus
  -> WithEnv CodePlus
toPiType ml xps n = do
  xps' <- mapM supplyName xps
  return (CodeMetaTerminal ml, CodePi xps' n)

supplyName ::
     Either DataPlus (Identifier, DataPlus) -> WithEnv (Identifier, DataPlus)
supplyName (Left t) = do
  x <- newNameWith "hole"
  return (x, t)
supplyName (Right (x, t)) = return (x, t)

typeOf :: CodePlus -> WithEnv DataPlus
typeOf (m, _) = extract $ fst $ obtainInfoCodeMeta m

toVar :: (Identifier, DataPlus) -> DataPlus
toVar (x, t) = do
  let (_, ml) = obtainInfoDataMeta $ fst t
  (DataMetaNonTerminal t ml, DataUpsilon x)

polarize' :: TermPlus -> WithEnv (DataPlus, (Identifier, CodePlus))
polarize' e@(m, _) = do
  e' <- polarize e
  (p, ml) <- polarizeMeta m
  x <- newNameWith "var"
  return ((posMeta p ml, DataUpsilon x), (x, e'))

bindLet :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
bindLet [] cont = return cont
bindLet ((x, e):xes) cont = do
  e' <- bindLet xes cont
  let (typeOfCont, ml) = obtainInfoCodeMeta $ fst e'
  p <- typeOf e
  -- kleisli extension (i.e. dependent up-elimination)
  let ke = (fst typeOfCont, CodeUpElim (x, p) e typeOfCont)
  return (negMeta ke ml, CodeUpElim (x, p) e e')

polarizePlus ::
     [(a, TermPlus)] -> WithEnv ([DataPlus], [(Identifier, CodePlus)], [a])
polarizePlus xts = do
  let (xs, ts) = unzip xts
  (ys', yts') <- unzip <$> mapM polarize' ts
  return (ys', yts', xs)

polarizePlus' :: [(a, TermPlus)] -> WithEnv [(a, DataPlus)]
polarizePlus' xts = do
  let (xs, ts) = unzip xts
  ps <- mapM (polarize >=> reduceCodePlus >=> extract) ts
  return $ zip xs ps

polarizeMeta :: Meta -> WithEnv (DataPlus, Maybe (Int, Int))
polarizeMeta m = do
  let (t, ml) = obtainInfoMeta m
  d <- polarize t >>= reduceCodePlus >>= extract
  return (d, ml)

extract :: CodePlus -> WithEnv DataPlus
extract e =
  case e of
    (_, CodeUpIntro d) -> return d
    _                  -> throwError "extract"

extractFromDownPi :: DataPlus -> WithEnv ([(Identifier, DataPlus)], CodePlus)
extractFromDownPi e =
  case e of
    (_, DataDown (_, CodePi xps n)) -> return (xps, n)
    _                               -> throwError "extract"

posMeta :: DataPlus -> Maybe (Int, Int) -> DataMeta
posMeta = DataMetaNonTerminal

negMeta :: CodePlus -> Maybe (Int, Int) -> CodeMeta
negMeta = CodeMetaNonTerminal

up :: DataPlus -> Maybe (Int, Int) -> CodePlus
up u ml = (CodeMetaTerminal ml, CodeUp u)

down :: CodePlus -> Maybe (Int, Int) -> DataPlus
down n ml = (DataMetaTerminal ml, DataDown n)

-- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv CodePlus
polarizeTheta m "core.i8.add"    = polarizeThetaArith ArithAdd m
polarizeTheta m "core.i16.add"   = polarizeThetaArith ArithAdd m
polarizeTheta m "core.i32.add"   = polarizeThetaArith ArithAdd m
polarizeTheta m "core.i64.add"   = polarizeThetaArith ArithAdd m
polarizeTheta m "core.i8.sub"    = polarizeThetaArith ArithSub m
polarizeTheta m "core.i16.sub"   = polarizeThetaArith ArithSub m
polarizeTheta m "core.i32.sub"   = polarizeThetaArith ArithSub m
polarizeTheta m "core.i64.sub"   = polarizeThetaArith ArithSub m
polarizeTheta m "core.i8.mul"    = polarizeThetaArith ArithMul m
polarizeTheta m "core.i16.mul"   = polarizeThetaArith ArithMul m
polarizeTheta m "core.i32.mul"   = polarizeThetaArith ArithMul m
polarizeTheta m "core.i64.mul"   = polarizeThetaArith ArithMul m
polarizeTheta m "core.i8.div"    = polarizeThetaArith ArithDiv m
polarizeTheta m "core.i16.div"   = polarizeThetaArith ArithDiv m
polarizeTheta m "core.i32.div"   = polarizeThetaArith ArithDiv m
polarizeTheta m "core.i64.div"   = polarizeThetaArith ArithDiv m
polarizeTheta m "core.print.i64" = polarizeThetaPrint m
polarizeTheta _ _                = throwError "polarize.theta"

polarizeThetaArith :: Arith -> Meta -> WithEnv CodePlus
polarizeThetaArith op m = do
  (upT, ml) <- polarizeMeta m
  case upT of
    d@(_, DataDown (_, CodePi _ (_, CodeUp int))) -> do
      (x, varX) <- newVarOfType int
      (y, varY) <- newVarOfType int
      return
        ( negMeta (up d ml) ml
        , CodeUpIntro
            ( posMeta d ml
            , DataDownIntroPiIntro
                [(x, int), (y, int)]
                (negMeta (up int ml) ml, CodeTheta (ThetaArith op varX varY))))
    _ -> throwError "polarize.theta.arith"

polarizeThetaPrint :: Meta -> WithEnv CodePlus
polarizeThetaPrint m = do
  (upT, ml) <- polarizeMeta m
  case upT of
    d@(_, DataDown (_, CodePi [(_, int)] cod)) -> do
      (x, varX) <- newVarOfType int
      return
        ( negMeta (up d ml) ml
        , CodeUpIntro
            ( posMeta d ml
            , DataDownIntroPiIntro
                [(x, int)]
                (negMeta cod ml, CodeTheta (ThetaPrint varX))))
    _ -> throwError "polarize.theta.print"

newVarOfType :: DataPlus -> WithEnv (Identifier, DataPlus)
newVarOfType t = do
  x <- newNameWith "arg"
  return (x, (posMeta t Nothing, DataUpsilon x))
