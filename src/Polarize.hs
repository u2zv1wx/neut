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
import           Reduce.Code

polarize :: TermPlus -> WithEnv CodePlus
polarize (_, TermTau) = exponentTrivial
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (u, ml) <- polarizeMeta m
  return (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataUpsilon x))
polarize (_, TermEpsilon _) = exponentTrivial
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
polarize (m, TermPi _ _) = do
  (u, ml) <- polarizeMeta m
  clsExp <- exponentClosure
  return (negMeta (up u ml) ml, CodeUpIntro clsExp)
polarize (m, TermPiIntro xts e) = do
  xps <- polarizePlus' xts
  e' <- polarize e
  lamName <- newNameWith "theta"
  makeClosure lamName m xps e'
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  es' <- mapM polarize es
  callClosure m e' es'
polarize (m, TermMu (f, t) e) = do
  (_, ml) <- polarizeMeta m
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  let (xs, ts) = unzip vs
  ts' <- mapM (polarize >=> reduceCodePlus >=> extract) ts
  let vs' = map toTermVar vs
  vs'' <- mapM polarize vs'
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
  cls <- makeClosure f clsMeta (zip xs ts') lamBody'
  callClosure m cls vs''

makeClosure ::
     Identifier
  -> Meta
  -> [(Identifier, DataPlus)]
  -> CodePlus
  -> WithEnv CodePlus
makeClosure lamThetaName m xps e = do
  (_, ml) <- polarizeMeta m
  let fvs = nubBy (\x y -> fst x == fst y) $ varCodePlus e
  -- envType = (C1, ..., Cn), where Ci is the types of the free variables in e'
  envExp <- exponentSigma $ map (Left . snd) fvs
  (envVarName, envVar) <- newVarOfType envExp
  let codType = fst $ obtainInfoCodeMeta $ fst e
  let lamBody = (negMeta codType ml, CodeSigmaElim fvs envVar e)
  -- ((A1, ..., An) -> ↑B) ~> ((ENV, A1, ..., An) -> ↑B)
  downPiExp <- exponentTrivialLabel
  let lamTheta = (posMeta downPiExp ml, DataTheta lamThetaName)
  -- lamThetaName ~> thunk (lam (envVarName, x1, ..., xn) lamBody)
  penv <- gets polEnv
  when (lamThetaName `elem` map fst penv) $
    insPolEnv lamThetaName ((envVarName, envExp) : xps) lamBody
  let fvSigmaIntro = (posMeta envExp ml, DataSigmaIntro $ map toVar fvs)
  -- piType'  : ↓(((C1, ..., Cn), A) -> ↑B)
  -- piType'' : ↓((typeVar, A) -> ↑B)
  -- i.e. piType' = piType'' {typeVar := (C1, ..., Cn)}
  clsExp <- exponentClosure
  return
    ( negMeta (up clsExp ml) ml
    , CodeUpIntro
        (posMeta clsExp ml, DataSigmaIntro [envExp, fvSigmaIntro, lamTheta]))

callClosure :: Meta -> CodePlus -> [CodePlus] -> WithEnv CodePlus
callClosure m e es = do
  (u, ml) <- polarizeMeta m
  ts <- mapM typeOf es
  triv <- exponentTrivialLabel
  (typeVarName, typeVar) <- newVarOfType triv
  -- let (_, mlPi) = obtainInfoCodeMeta funMeta
  -- downPiType <- reduceCodePlus upDownPiType >>= extract
  -- (xpsPi, codType) <- extractFromDownPi downPiType
  downPiType'' <- exponentTrivialLabel
  clsType <- exponentClosure
  argList <- mapM newVarOfType ts
  (clsVarName, clsVar) <- newVarOfType clsType
  (lamVarName, lamVar) <- newVarOfType downPiType''
  (envVarName, envVar) <- newVarOfType typeVar
  cont <-
    bindLet
      (zip (map fst argList) es)
      ( negMeta (up u ml) ml
      , CodeSigmaElim
          [ (typeVarName, triv)
          , (lamVarName, downPiType'')
          , (envVarName, typeVar)
          ]
          clsVar
          ( negMeta (up u ml) ml
          , CodePiElimDownElim lamVar (envVar : map toVar argList)))
  return (negMeta (up u ml) ml, CodeUpElim (clsVarName, clsType) e cont)

-- toSigmaType ::
--      Maybe (Int, Int)
--   -> [Either DataPlus (Identifier, DataPlus)]
--   -> WithEnv DataPlus
-- toSigmaType ml xps = do
--   xps' <- mapM supplyName xps
--   return (DataMetaTerminal ml, DataSigma xps')
-- supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
-- supplyName (Left t) = do
--   x <- newNameWith "hole"
--   return (x, t)
-- supplyName (Right (x, t)) = return (x, t)
typeOf :: CodePlus -> WithEnv DataPlus
typeOf (m, _) = extract $ fst $ obtainInfoCodeMeta m

toVar :: (Identifier, DataPlus) -> DataPlus
toVar (x, t) = do
  let (_, ml) = obtainInfoDataMeta $ fst t
  (DataMetaNonTerminal t ml, DataUpsilon x)

toTermVar :: (Identifier, TermPlus) -> TermPlus
toTermVar (x, t) = do
  let (_, ml) = obtainInfoMeta $ fst t
  (MetaNonTerminal t ml, TermUpsilon x)

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

-- polarizePlus ::
--      [(a, TermPlus)] -> WithEnv ([DataPlus], [(Identifier, CodePlus)], [a])
-- polarizePlus xts = do
--   let (xs, ts) = unzip xts
--   (ys', yts') <- unzip <$> mapM polarize' ts
--   return (ys', yts', xs)
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

posMeta :: DataPlus -> Maybe (Int, Int) -> DataMeta
posMeta = DataMetaNonTerminal

negMeta :: CodePlus -> Maybe (Int, Int) -> CodeMeta
negMeta = CodeMetaNonTerminal

up :: DataPlus -> Maybe (Int, Int) -> CodePlus
up u ml = (CodeMetaTerminal ml, CodeUp u)

-- return LABEL_OF_TRIVAL_EXPONENT
-- (LABEL_OF_TRIVAL_EXPONENT ~> lam (n, x). (x, ..., x))
exponentTrivialLabel :: WithEnv DataPlus
exponentTrivialLabel = undefined

exponentTrivial :: WithEnv CodePlus
exponentTrivial = do
  triv <- exponentTrivialLabel
  return (negMeta (up triv Nothing) Nothing, CodeUpIntro triv)

exponentSigma :: [Either DataPlus (Identifier, DataPlus)] -> WithEnv DataPlus
exponentSigma = undefined

exponentClosure :: WithEnv DataPlus
exponentClosure = do
  triv <- exponentTrivialLabel
  (typeVarName, typeVar) <- newVarOfType triv
  exponentSigma [Right (typeVarName, triv), Left typeVar, Left triv]

-- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv CodePlus
polarizeTheta m name@"core.i8.add"    = polarizeThetaArith name ArithAdd m
polarizeTheta m name@"core.i16.add"   = polarizeThetaArith name ArithAdd m
polarizeTheta m name@"core.i32.add"   = polarizeThetaArith name ArithAdd m
polarizeTheta m name@"core.i64.add"   = polarizeThetaArith name ArithAdd m
polarizeTheta m name@"core.i8.sub"    = polarizeThetaArith name ArithSub m
polarizeTheta m name@"core.i16.sub"   = polarizeThetaArith name ArithSub m
polarizeTheta m name@"core.i32.sub"   = polarizeThetaArith name ArithSub m
polarizeTheta m name@"core.i64.sub"   = polarizeThetaArith name ArithSub m
polarizeTheta m name@"core.i8.mul"    = polarizeThetaArith name ArithMul m
polarizeTheta m name@"core.i16.mul"   = polarizeThetaArith name ArithMul m
polarizeTheta m name@"core.i32.mul"   = polarizeThetaArith name ArithMul m
polarizeTheta m name@"core.i64.mul"   = polarizeThetaArith name ArithMul m
polarizeTheta m name@"core.i8.div"    = polarizeThetaArith name ArithDiv m
polarizeTheta m name@"core.i16.div"   = polarizeThetaArith name ArithDiv m
polarizeTheta m name@"core.i32.div"   = polarizeThetaArith name ArithDiv m
polarizeTheta m name@"core.i64.div"   = polarizeThetaArith name ArithDiv m
polarizeTheta m name@"core.f32.add"   = polarizeThetaArith name ArithAdd m
polarizeTheta m name@"core.f64.add"   = polarizeThetaArith name ArithAdd m
polarizeTheta m name@"core.f32.sub"   = polarizeThetaArith name ArithSub m
polarizeTheta m name@"core.f64.sub"   = polarizeThetaArith name ArithSub m
polarizeTheta m name@"core.f32.mul"   = polarizeThetaArith name ArithMul m
polarizeTheta m name@"core.f64.mul"   = polarizeThetaArith name ArithMul m
polarizeTheta m name@"core.f32.div"   = polarizeThetaArith name ArithDiv m
polarizeTheta m name@"core.f64.div"   = polarizeThetaArith name ArithDiv m
polarizeTheta m name@"core.print.i64" = polarizeThetaPrint name m
polarizeTheta _ _                     = throwError "polarize.theta"

polarizeThetaArith :: Identifier -> Arith -> Meta -> WithEnv CodePlus
polarizeThetaArith name op m = do
  (_, ml) <- polarizeMeta m
  numExp <- exponentTrivialLabel
  (x, varX) <- newVarOfType numExp
  (y, varY) <- newVarOfType numExp
  makeClosure
    name
    m
    [(x, numExp), (y, numExp)]
    (negMeta (up numExp ml) ml, CodeTheta (ThetaArith op varX varY))

polarizeThetaPrint :: Identifier -> Meta -> WithEnv CodePlus
polarizeThetaPrint name m = do
  (_, ml) <- polarizeMeta m
  intExp <- exponentTrivialLabel
  codExp <- exponentTrivial
  (x, varX) <- newVarOfType intExp
  makeClosure
    name
    m
    [(x, intExp)]
    (negMeta codExp ml, CodeTheta (ThetaPrint varX))

newVarOfType :: DataPlus -> WithEnv (Identifier, DataPlus)
newVarOfType t = do
  x <- newNameWith "arg"
  return (x, (posMeta t Nothing, DataUpsilon x))
