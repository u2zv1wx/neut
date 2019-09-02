-- This module "polarizes" a neutral term into a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value. A detailed explanation of Call-By-Push-Value can be found
-- in P. Levy, "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis,
-- Queen Mary College, 2001.
module Polarize
  ( polarize
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Prelude              hiding (pi)

import           Data.Basic
import           Data.Code
import           Data.Env
import           Data.List            (nubBy)
import           Data.Term

polarize :: TermPlus -> WithEnv CodePlus
polarize (m, TermTau) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataTau))
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataUpsilon x))
polarize (m, TermEpsilon x) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataEpsilon x))
polarize (m, TermEpsilonIntro l) = do
  let (t, ml) = obtainInfoMeta m
  (xts, x) <- polarize' t
  return $ bindLet xts (ml, CodeUpIntro (ml, DataEpsilonIntro l x))
polarize (m, TermEpsilonElim (x, t) e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (yts, y) <- polarize' e
  (zts, z) <- polarize' t
  let ml = snd $ obtainInfoMeta m
  return $ bindLet (yts ++ zts) (ml, CodeEpsilonElim (x, z) y (zip cs es'))
polarize (m, TermPi xts) = do
  let ml = snd $ obtainInfoMeta m
  let (xs, ts) = unzip xts
  ns <- mapM (upElimUp ml) ts
  let downPiType = (ml, DataDownPi $ zip xs ns)
  (envVarName, envVar) <- newDataUpsilon
  closureType <-
    toSigmaType
      ml
      [Right (envVarName, (ml, DataTau)), Left envVar, Left downPiType]
  return (ml, CodeUpIntro closureType)
polarize (m, TermPiIntro xts e) = do
  let xs = map fst xts
  -- let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  -- let fvs = filter (\(x, _) -> x `notElem` xs) vs
  let fvs = obtainFreeVarList xs e
  e' <- polarize e
  makeClosureNonRec Nothing fvs m xs e'
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  callClosure m e' es
polarize (m, TermMu (f, t) e) = do
  let ml = snd $ obtainInfoMeta m
  -- let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  let fvs = obtainFreeVarList [f] e
  let fvs' = map toTermUpsilon fvs
  -- let clsMuType = (MetaTerminal ml, TermPi vs t)
  let clsMuType = (MetaTerminal ml, undefined)
  let lamBody =
        substTermPlus
          [ ( f
            , ( MetaNonTerminal t ml
              , TermPiElim (MetaNonTerminal clsMuType ml, TermTheta f) fvs'))
          ]
          e
  let clsMeta = MetaNonTerminal clsMuType ml
  -- let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus lamBody
  -- let fvs = filter (\(y, _) -> y /= f) vs
  -- let fvs = obtainFreeVarList [f] lamBody
  -- cls <- makeClosure f clsMeta (map fst vs) lamBody
  lamBody' <- polarize lamBody
  cls <- makeClosureNonRec (Just f) fvs clsMeta [f] lamBody'
  callClosure m cls fvs'

obtainFreeVarList :: [Identifier] -> TermPlus -> [(Identifier, TermPlus)]
obtainFreeVarList xs e = do
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  filter (\(x, _) -> x `notElem` xs) vs

type Binder = [(Identifier, CodePlus)]

polarize' :: TermPlus -> WithEnv (Binder, DataPlus)
polarize' e@(m, _) = do
  e' <- polarize e
  (varName, var) <- newDataUpsilon' $ snd $ obtainInfoMeta m
  return ([(varName, e')], var)

upElimUp :: Maybe Loc -> TermPlus -> WithEnv CodePlus
upElimUp ml e = do
  e' <- polarize e
  (varName, var) <- newDataUpsilon' ml
  return (ml, CodeUpElim varName e' (ml, CodeUp var))

-- makeClosure ::
--      Identifier -> Meta -> [Identifier] -> TermPlus -> WithEnv CodePlus
-- makeClosure lamThetaName m xs e = do
--   let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
--   let fvs = filter (\(x, _) -> x `notElem` xs) vs
--   e' <- polarize e
--   let ml = snd $ obtainInfoMeta m
--   let (freeVarNameList, freeVarTypeList) = unzip fvs
--   (yess, ys) <- unzip <$> mapM polarize' freeVarTypeList
--   envExp <- toSigmaType ml $ map Left ys
--   (envVarName, envVar) <- newDataUpsilon
--   let lamBody = (ml, CodeSigmaElim (map fst fvs) envVar e')
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
--   makeClosure' fvs lamThetaName m xs e'
-- makeClosure' ::
--      [(Identifier, TermPlus)]
--   -> Identifier
--   -> Meta
--   -> [Identifier]
--   -> CodePlus
--   -> WithEnv CodePlus
-- makeClosure' fvs lamThetaName m xs e = do
makeClosureNonRec ::
     Maybe Identifier
  -> [(Identifier, TermPlus)]
  -> Meta
  -> [Identifier]
  -> CodePlus
  -> WithEnv CodePlus
makeClosureNonRec mName fvs m xs e = do
  let ml = snd $ obtainInfoMeta m
  let (freeVarNameList, freeVarTypeList) = unzip fvs
  (yess, ys) <- unzip <$> mapM polarize' freeVarTypeList
  envExp <- toSigmaType ml $ map Left ys
  (envVarName, envVar) <- newDataUpsilon
  let lamBody = (ml, CodeSigmaElim (map fst fvs) envVar e)
  let fvSigmaIntro =
        ( ml
        , DataSigmaIntro $
          zipWith (curry toDataUpsilon) freeVarNameList (map fst ys))
  case mName of
    Nothing -> do
      let lam = (ml, DataDownIntroPiIntro (envVarName : xs) lamBody)
      return $
        bindLet
          (concat yess)
          (ml, CodeUpIntro (ml, DataSigmaIntro [envExp, fvSigmaIntro, lam]))
    Just lamThetaName -> do
      let lamTheta = (ml, DataTheta lamThetaName)
      penv <- gets polEnv
      when (lamThetaName `elem` map fst penv) $
        insPolEnv lamThetaName (envVarName : xs) lamBody
      return $
        bindLet
          (concat yess)
          ( ml
          , CodeUpIntro (ml, DataSigmaIntro [envExp, fvSigmaIntro, lamTheta]))

callClosure :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure m e es = do
  (xess, xs) <- unzip <$> mapM polarize' es
  let ml = snd $ obtainInfoMeta m
  (clsVarName, clsVar) <- newDataUpsilon
  (typeVarName, _) <- newDataUpsilon
  (envVarName, envVar) <- newDataUpsilon
  (lamVarName, lamVar) <- newDataUpsilon
  return
    ( ml
    , CodeUpElim
        clsVarName
        e
        (bindLet
           (concat xess)
           ( ml
           , CodeSigmaElim
               -- optimizable: ここでのtypevarの取得は省略可能
               [typeVarName, envVarName, lamVarName]
               clsVar
               (ml, CodePiElimDownElim lamVar (envVar : xs)))))

bindLet :: Binder -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = do
  let e' = bindLet xes cont
  (fst e', CodeUpElim x e e')

toSigmaType ::
     Maybe (Int, Int)
  -> [Either DataPlus (Identifier, DataPlus)]
  -> WithEnv DataPlus
toSigmaType ml xps = do
  xps' <- mapM supplyName xps
  return (ml, DataSigma xps')

supplyName :: Either b (Identifier, b) -> WithEnv (Identifier, b)
supplyName (Right (x, t)) = return (x, t)
supplyName (Left t) = do
  x <- newNameWith "hole"
  return (x, t)

-- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv CodePlus
polarizeTheta m name@"core.i8.add" = polarizeThetaArith name ArithAdd (int 8) m
polarizeTheta m name@"core.i16.add" =
  polarizeThetaArith name ArithAdd (int 16) m
polarizeTheta m name@"core.i32.add" =
  polarizeThetaArith name ArithAdd (int 32) m
polarizeTheta m name@"core.i64.add" =
  polarizeThetaArith name ArithAdd (int 64) m
polarizeTheta m name@"core.i8.sub" = polarizeThetaArith name ArithSub (int 8) m
polarizeTheta m name@"core.i16.sub" =
  polarizeThetaArith name ArithSub (int 16) m
polarizeTheta m name@"core.i32.sub" =
  polarizeThetaArith name ArithSub (int 32) m
polarizeTheta m name@"core.i64.sub" =
  polarizeThetaArith name ArithSub (int 64) m
polarizeTheta m name@"core.i8.mul" = polarizeThetaArith name ArithMul (int 8) m
polarizeTheta m name@"core.i16.mul" =
  polarizeThetaArith name ArithMul (int 16) m
polarizeTheta m name@"core.i32.mul" =
  polarizeThetaArith name ArithMul (int 32) m
polarizeTheta m name@"core.i64.mul" =
  polarizeThetaArith name ArithMul (int 64) m
polarizeTheta m name@"core.i8.div" = polarizeThetaArith name ArithDiv (int 8) m
polarizeTheta m name@"core.i16.div" =
  polarizeThetaArith name ArithDiv (int 16) m
polarizeTheta m name@"core.i32.div" =
  polarizeThetaArith name ArithDiv (int 32) m
polarizeTheta m name@"core.i64.div" =
  polarizeThetaArith name ArithDiv (int 64) m
polarizeTheta m name@"core.f32.add" =
  polarizeThetaArith name ArithAdd (float 32) m
polarizeTheta m name@"core.f64.add" =
  polarizeThetaArith name ArithAdd (float 64) m
polarizeTheta m name@"core.f32.sub" =
  polarizeThetaArith name ArithSub (float 32) m
polarizeTheta m name@"core.f64.sub" =
  polarizeThetaArith name ArithSub (float 64) m
polarizeTheta m name@"core.f32.mul" =
  polarizeThetaArith name ArithMul (float 32) m
polarizeTheta m name@"core.f64.mul" =
  polarizeThetaArith name ArithMul (float 64) m
polarizeTheta m name@"core.f32.div" =
  polarizeThetaArith name ArithDiv (float 32) m
polarizeTheta m name@"core.f64.div" =
  polarizeThetaArith name ArithDiv (float 64) m
polarizeTheta m name@"core.print.i64" = polarizeThetaPrint name m
polarizeTheta _ _ = throwError "polarize.theta"

int :: Int -> DataPlus
int i = (Nothing, DataEpsilon $ "i" ++ show i)

float :: Int -> DataPlus
float i = (Nothing, DataEpsilon $ "f" ++ show i)

polarizeThetaArith ::
     Identifier -> Arith -> DataPlus -> Meta -> WithEnv CodePlus
polarizeThetaArith name op lowType m = do
  let ml = snd $ obtainInfoMeta m
  (x, varX) <- newDataUpsilon
  (y, varY) <- newDataUpsilon
  makeClosureNonRec
    (Just name)
    []
    m
    [x, y]
    (ml, CodeTheta (ThetaArith op lowType varX varY))

polarizeThetaPrint :: Identifier -> Meta -> WithEnv CodePlus
polarizeThetaPrint name m = do
  let ml = snd $ obtainInfoMeta m
  (x, varX) <- newDataUpsilon
  makeClosureNonRec (Just name) [] m [x] (ml, CodeTheta (ThetaPrint varX))

newDataUpsilon :: WithEnv (Identifier, DataPlus)
newDataUpsilon = newDataUpsilon' Nothing

newDataUpsilon' :: Maybe Loc -> WithEnv (Identifier, DataPlus)
newDataUpsilon' ml = do
  x <- newNameWith "arg"
  return (x, (ml, DataUpsilon x))
