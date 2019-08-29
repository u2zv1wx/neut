-- This module "polarizes" a neutral term into a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value. A detailed explanation of Call-By-Push-Value can be found
-- in P. Levy, "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis,
-- Queen Mary College, 2001.
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
  exponentImmediate >>= \i -> return (Nothing, CodeUpIntro i)
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (y, yts, ml) <- polarizeMeta m
  return $
    bindLet yts (ml, CodeUpIntro (DataMetaNonTerminal y ml, DataUpsilon x))
polarize (_, TermEpsilon _) =
  exponentImmediate >>= \i -> return (Nothing, CodeUpIntro i)
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
  lamName <- newNameWith "theta"
  makeClosure lamName m (map fst xts) e
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  callClosure m e' es
polarize (m, TermMu (f, t) e) = do
  let ml = snd $ obtainInfoMeta m
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  let vs' = map toTermUpsilon vs
  let clsMuType = (MetaTerminal ml, TermPi vs t)
  let lamBody =
        substTermPlus
          [ ( f
            , ( MetaNonTerminal t ml
              , TermPiElim (MetaNonTerminal clsMuType ml, TermTheta f) vs'))
          ]
          e
  let clsMeta = MetaNonTerminal clsMuType ml
  cls <- makeClosure f clsMeta (map fst vs) lamBody
  callClosure m cls vs'

type Binder = [(Identifier, CodePlus)]

polarize' :: TermPlus -> WithEnv (Binder, DataPlus)
polarize' e@(m, _) = do
  e' <- polarize e
  case m of
    MetaTerminal ml -> do
      i <- exponentImmediate
      (varName, var) <- newDataUpsilon' i ml
      return ([(varName, e')], var)
    MetaNonTerminal t ml -> do
      (xes, x) <- polarize' t
      (varName, var) <- newDataUpsilon' x ml
      return (xes ++ [(varName, e')], var)

polarizeMeta :: Meta -> WithEnv (DataPlus, Binder, Maybe Loc)
polarizeMeta m = do
  (xes, x) <- polarize' $ fst $ obtainInfoMeta m
  let ml = snd $ obtainInfoMeta m
  return (x, xes, ml)

makeClosure ::
     Identifier -> Meta -> [Identifier] -> TermPlus -> WithEnv CodePlus
makeClosure lamThetaName m xs e = do
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  let fvs = filter (\(x, _) -> x `notElem` xs) vs
  e' <- polarize e
  makeClosure' fvs lamThetaName m xs e'

makeClosure' ::
     [(Identifier, TermPlus)]
  -> Identifier
  -> Meta
  -> [Identifier]
  -> CodePlus
  -> WithEnv CodePlus
makeClosure' fvs lamThetaName m xs e = do
  let ml = snd $ obtainInfoMeta m
  let (freeVarNameList, freeVarTypeList) = unzip fvs
  (yess, ys) <- unzip <$> mapM polarize' freeVarTypeList
  envExpName <- newNameWith "exp"
  envExp <- exponentSigma envExpName ml $ map Left ys
  (envVarName, envVar) <- newDataUpsilon envExp
  let lamBody = (ml, CodeSigmaElim (map fst fvs) envVar e)
  i <- exponentImmediate
  let lamTheta = (DataMetaNonTerminal i ml, DataTheta lamThetaName)
  penv <- gets polEnv
  when (lamThetaName `elem` map fst penv) $
    insPolEnv lamThetaName (envVarName : xs) lamBody
  let fvSigmaIntro =
        ( DataMetaNonTerminal envExp ml
        , DataSigmaIntro $ zipWith (curry toDataUpsilon) freeVarNameList ys)
  clsExp <- exponentClosure
  return $
    bindLet
      (concat yess)
      ( ml
      , CodeUpIntro
          ( DataMetaNonTerminal clsExp ml
          , DataSigmaIntro [envExp, fvSigmaIntro, lamTheta]))

callClosure :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure m e es = do
  (xess, xs) <- unzip <$> mapM polarize' es
  let ml = snd $ obtainInfoMeta m
  i <- exponentImmediate
  clsExp <- exponentClosure
  (clsVarName, clsVar) <- newDataUpsilon clsExp
  (typeVarName, typeVar) <- newDataUpsilon i
  (envVarName, envVar) <- newDataUpsilon typeVar
  (lamVarName, lamVar) <- newDataUpsilon i
  return
    ( ml
    , CodeUpElim
        clsVarName
        e
        (bindLet
           (concat xess)
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

exponentImmediate :: WithEnv DataPlus
exponentImmediate =
  return (DataMetaTerminal Nothing, DataTheta "EXPONENT.IMMEDIATE")

-- Sigma (y1 : t1, ..., yn : tn) ~>
--   lam (m, z).
--     let (y1, ..., yn) := z in
--     bind ys1 = t1 @ (m, y1) in
--     ...
--     bind ysn = tn @ (m, yn) in -- ここまではコードとしてstaticに書ける
--     let (ys1-1, ..., ys1-m) := ys1 in -- ここでm-elimが必要になる。
--     ...
--     let (ysn-1, ..., ysn-m) := ysn in
--     ((ys1-1, ..., ysn-1), ..., (ys1-m, ..., ysn-m))
--
-- (Note that Sigma (y1 : t1, ..., yn : tn) must be closed.)
exponentSigma ::
     Identifier
  -> Maybe Loc
  -> [Either DataPlus (Identifier, DataPlus)]
  -> WithEnv DataPlus
exponentSigma lamThetaName ml mxts = do
  penv <- gets polEnv
  i <- exponentImmediate
  let sigmaExp = (DataMetaNonTerminal i ml, DataTheta lamThetaName)
  case lookup lamThetaName penv of
    Just _ -> return sigmaExp
    Nothing -> do
      xts <- mapM supplyName mxts
      (countVarName, countVar) <- newDataUpsilon i
      (sigVarName, sigVar) <- newDataUpsilon sigmaExp
      let appList =
            map
              (\(x, t) ->
                 (ml, CodePiElimDownElim t [countVar, toDataUpsilon (x, t)]))
              xts
      ys <- mapM (const $ newNameWith "var") xts
      let lamBody =
            ( ml
            , CodeSigmaElim
                (map fst xts)
                sigVar
                (bindLet (zip ys appList) undefined))
      insPolEnv lamThetaName [countVarName, sigVarName] lamBody
      return sigmaExp

exponentClosure :: WithEnv DataPlus
exponentClosure = do
  i <- exponentImmediate
  (typeVarName, typeVar) <- newDataUpsilon i
  exponentSigma
    "EXPONENT.CLOSURE"
    Nothing
    [Right (typeVarName, i), Left typeVar, Left i]

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
  numExp <- exponentImmediate
  (x, varX) <- newDataUpsilon numExp
  (y, varY) <- newDataUpsilon numExp
  makeClosure' [] name m [x, y] (ml, CodeTheta (ThetaArith op varX varY))

polarizeThetaPrint :: Identifier -> Meta -> WithEnv CodePlus
polarizeThetaPrint name m = do
  let ml = snd $ obtainInfoMeta m
  intExp <- exponentImmediate
  (x, varX) <- newDataUpsilon intExp
  makeClosure' [] name m [x] (ml, CodeTheta (ThetaPrint varX))

newDataUpsilon :: DataPlus -> WithEnv (Identifier, DataPlus)
newDataUpsilon t = newDataUpsilon' t Nothing

newDataUpsilon' :: DataPlus -> Maybe Loc -> WithEnv (Identifier, DataPlus)
newDataUpsilon' t ml = do
  x <- newNameWith "arg"
  return (x, (DataMetaNonTerminal t ml, DataUpsilon x))
