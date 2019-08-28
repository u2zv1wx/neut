-- This module "polarizes" a neutral term into a negMetaative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value, although this translation doesn't preserve types when the
-- given term includes dependent sigma-elimination. A detailed explanation of
-- Call-By-Push-Value can be found in P. Levy, "Call-by-Push-Value: A Subsuming
-- Paradigm". Ph. D. thesis, Queen Mary College, 2001.
--
-- Every type is converted into an "exponent", which is a function that receives
-- an integer `n` and a term `e` of that type, and returns n-copy of `e`, namely,
-- returns (e, ..., e). This operation roughly corresponds to eta-expansion. Indeed,
-- when the integer `n` equals to 1, this exponential operation degenerates to
-- eta-expansion.
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
polarize (_, TermTau) =
  exponentTrivial >>= \triv -> return (Nothing, CodeUpIntro triv)
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (y, yts, ml) <- polarizeMeta m
  return $
    bindLet yts (ml, CodeUpIntro (DataMetaNonTerminal y ml, DataUpsilon x))
polarize (_, TermEpsilon _) =
  exponentTrivial >>= \triv -> return (Nothing, CodeUpIntro triv)
polarize (m, TermEpsilonIntro l) = do
  (u, ues, ml) <- polarizeMeta m
  return $
    bindLet ues (ml, CodeUpIntro (DataMetaNonTerminal u ml, DataEpsilonIntro l))
polarize (m, TermEpsilonElim (x, t) e bs) = do
  let ml = snd $ obtainInfoMeta m
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (yts, y) <- polarize' e
  (zts, z) <- polarize' t
  return $ bindLet (yts ++ zts) (ml, CodeEpsilonElim (x, z) y (zip cs es'))
polarize (m, TermPi _ _) = do
  (_, _, ml) <- polarizeMeta m
  clsExp <- exponentClosure
  return (ml, CodeUpIntro clsExp)
polarize (m, TermPiIntro xts e) = do
  e' <- polarize e
  lamName <- newNameWith "theta"
  makeClosure lamName m (map fst xts) e'
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  callClosure m e' es
polarize (m, TermMu (f, t) e) = do
  let ml = snd $ obtainInfoMeta m
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  let (xs, _) = unzip vs
  let vs' = map toTermUpsilon vs
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
  cls <- makeClosure f clsMeta xs lamBody'
  callClosure m cls vs'

type Binder = [(Identifier, CodePlus)]

polarize' :: TermPlus -> WithEnv (Binder, DataPlus)
polarize' e@(m, _) = do
  e' <- polarize e
  case m of
    MetaTerminal ml -> do
      let triv = (DataMetaTerminal ml, DataTheta "THETA")
      (varName, var) <- newVarOfType' triv ml
      return ([(varName, e')], var)
    MetaNonTerminal t ml -> do
      (xes, x) <- polarize' t
      (varName, var) <- newVarOfType' x ml
      return (xes ++ [(varName, e')], var)

polarizeMeta :: Meta -> WithEnv (DataPlus, Binder, Maybe (Int, Int))
polarizeMeta m = do
  (xes, x) <- polarize' $ fst $ obtainInfoMeta m
  let ml = snd $ obtainInfoMeta m
  return (x, xes, ml)

makeClosure ::
     Identifier -> Meta -> [Identifier] -> CodePlus -> WithEnv CodePlus
makeClosure lamThetaName m xps e = do
  let ml = snd $ obtainInfoMeta m
  let fvs = nubBy (\x y -> fst x == fst y) $ varCodePlus e
  envExp <- exponentSigma ml $ map (Left . snd) fvs
  (envVarName, envVar) <- newVarOfType envExp
  let lamBody = (ml, CodeSigmaElim (map fst fvs) envVar e)
  triv <- exponentTrivial
  let lamTheta = (DataMetaNonTerminal triv ml, DataTheta lamThetaName)
  penv <- gets polEnv
  when (lamThetaName `elem` map fst penv) $
    insPolEnv lamThetaName (envVarName : xps) lamBody
  let fvSigmaIntro =
        (DataMetaNonTerminal envExp ml, DataSigmaIntro $ map toDataUpsilon fvs)
  clsExp <- exponentClosure
  return
    ( ml
    , CodeUpIntro
        ( DataMetaNonTerminal clsExp ml
        , DataSigmaIntro [envExp, fvSigmaIntro, lamTheta]))

callClosure :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure m e es = do
  (xes, xs) <- unzip <$> mapM polarize' es
  (_, ues, ml) <- polarizeMeta m
  triv <- exponentTrivial
  clsType <- exponentClosure
  (clsVarName, clsVar) <- newVarOfType clsType
  (typeVarName, typeVar) <- newVarOfType triv
  (envVarName, envVar) <- newVarOfType typeVar
  (lamVarName, lamVar) <- newVarOfType triv
  return $
    bindLet
      ues
      ( ml
      , CodeUpElim
          clsVarName
          e
          (bindLet
             (concat xes)
             ( ml
             , CodeSigmaElim
                 [typeVarName, envVarName, lamVarName]
                 clsVar
                 (ml, CodePiElimDownElim lamVar (envVar : xs)))))

bindLet :: Binder -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = do
  let e' = bindLet xes cont
  (fst e', CodeUpElim x e e')

-- return LABEL_OF_TRIVAL_EXPONENT
-- (LABEL_OF_TRIVAL_EXPONENT ~> lam (n, x). (x, ..., x))
exponentTrivial :: WithEnv DataPlus
exponentTrivial = return (DataMetaTerminal Nothing, DataTheta "_TRIVIAL_")

-- Sigma (y1 : t1, ..., yn : tn) ~>
--   lam (n, z).
--     let (y1, ..., yn) := z in
--     bind ys1 = t1 @ (n, y1) in
--     ...
--     bind ysn = tn @ (n, yn) in
--     ((ys1[0], ..., ysm[0]), ..., (ys1[n], ..., ysm[n]))
--
-- (Note that Sigma (y1 : t1, ..., yn : tn) must be closed.)
exponentSigma ::
     Maybe (Int, Int)
  -> [Either DataPlus (Identifier, DataPlus)]
  -> WithEnv DataPlus
exponentSigma ml mxts = do
  xts <- mapM supplyName mxts
  triv <- exponentTrivial
  lamThetaName <- newNameWith "exp.sigma"
  (countVarName, countVar) <- newVarOfType triv -- int
  let sigmaExp = (DataMetaNonTerminal triv Nothing, DataTheta lamThetaName)
  (sigVarName, sigVar) <- newVarOfType sigmaExp
  let lamBody =
        (ml, CodeSigmaElim (map fst xts) sigVar (undefined xts countVar))
  insPolEnv lamThetaName [countVarName, sigVarName] lamBody
  return sigmaExp

-- FIXME: 同じ関数を使い回すように変更すべき
exponentClosure :: WithEnv DataPlus
exponentClosure = do
  triv <- exponentTrivial
  (typeVarName, typeVar) <- newVarOfType triv
  exponentSigma Nothing [Right (typeVarName, triv), Left typeVar, Left triv]

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Right (x, t)) = return (x, t)
supplyName (Left t) = do
  x <- newNameWith "hole"
  return (x, t)

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
  let ml = snd $ obtainInfoMeta m
  numExp <- exponentTrivial
  (x, varX) <- newVarOfType numExp
  (y, varY) <- newVarOfType numExp
  makeClosure name m [x, y] (ml, CodeTheta (ThetaArith op varX varY))

polarizeThetaPrint :: Identifier -> Meta -> WithEnv CodePlus
polarizeThetaPrint name m = do
  let ml = snd $ obtainInfoMeta m
  intExp <- exponentTrivial
  (x, varX) <- newVarOfType intExp
  makeClosure name m [x] (ml, CodeTheta (ThetaPrint varX))

newVarOfType :: DataPlus -> WithEnv (Identifier, DataPlus)
newVarOfType t = newVarOfType' t Nothing

newVarOfType' :: DataPlus -> Maybe (Int, Int) -> WithEnv (Identifier, DataPlus)
newVarOfType' t ml = do
  x <- newNameWith "arg"
  return (x, (DataMetaNonTerminal t ml, DataUpsilon x))
