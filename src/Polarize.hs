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
  , inline
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Prelude              hiding (pi)

import           Data.Basic
import           Data.Code
import           Data.Comp
import           Data.Env
import           Data.List            (nubBy)
import           Data.Term
import           Reduce.Code

inline :: WithEnv ()
inline = do
  penv <- gets polEnv
  forM_ penv $ \(thetaName, (args, body)) -> do
    body' <- inlineCodePlus body
    unless (checkSanityCode body') $ throwError "sanity"
    body'' <- processCode body'
    insCompEnv thetaName args body''

processData :: DataPlus -> WithEnv ValuePlus
processData (_, DataImmediate)            = exponentImmediate
processData (_, DataTheta _)              = undefined
processData (_, DataUpsilon _)            = undefined
processData (_, DataEpsilon _)            = exponentImmediate
processData (_, DataEpsilonIntro _ _)     = undefined
processData (_, DataDownIntroPiIntro _ _) = undefined
processData (_, DataSigma xts)            = undefined
processData (_, DataSigmaIntro _)         = undefined

processCode :: CodePlus -> WithEnv CompPlus
processCode (m, CodeTheta theta) = do
  theta' <- processTheta theta
  return (m, CompTheta theta')
processCode (_, CodeEpsilonElim {}) = undefined
processCode (_, CodePiElimDownElim {}) = undefined
processCode (_, CodeSigmaElim {}) = undefined
processCode (_, CodeUpIntro {}) = undefined
processCode (_, CodeUpElim {}) = undefined

processTheta :: Theta -> WithEnv ValueTheta
processTheta = undefined

checkSanityData :: DataPlus -> Bool
checkSanityData (_, DataEpsilonIntro _ p) = null $ varDataPlus p
checkSanityData (_, DataSigma xts) = do
  let (xs, ts) = unzip xts
  all (`elem` xs) (concatMap varDataPlus ts) -- sigma must be closed
checkSanityData _ = True

checkSanityCode :: CodePlus -> Bool
checkSanityCode (_, CodeTheta _) = True
checkSanityCode (_, CodeEpsilonElim _ d branchList) = do
  let (_, es) = unzip branchList
  checkSanityData d && all checkSanityCode es
checkSanityCode (_, CodePiElimDownElim d ds) =
  checkSanityData d && all checkSanityData ds
checkSanityCode (_, CodeSigmaElim _ v e) =
  checkSanityData v && checkSanityCode e
checkSanityCode (_, CodeUpIntro v) = checkSanityData v
checkSanityCode (_, CodeUpElim _ e1 e2) =
  checkSanityCode e1 && checkSanityCode e2

polarize :: TermPlus -> WithEnv CodePlus
polarize (m, TermTau) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataImmediate))
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
polarize (m, TermPi _ _) = do
  let ml = snd $ obtainInfoMeta m
  envVarName <- newNameWith "gamma"
  let envVar = (ml, DataUpsilon envVarName)
  tmp1 <- newNameWith "tmp"
  tmp2 <- newNameWith "tmp"
  return
    ( ml
    , CodeUpIntro
        ( ml
        , DataSigma
            [ (envVarName, (ml, DataImmediate))
            , (tmp1, envVar) -- list of free variables
            , (tmp2, (ml, DataImmediate)) -- label to function
            ]))
polarize (m, TermPiIntro xts e) = do
  let xs = map fst xts
  let vs = nubBy (\x y -> fst x == fst y) $ varTermPlus e
  let fvs = filter (\(x, _) -> x `notElem` xs) vs
  e' <- polarize e
  makeClosureNonRec fvs m xs e'
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
  (varName, var) <- newDataUpsilon' $ snd $ obtainInfoMeta m
  return ([(varName, e')], var)

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
  envExp <- toSigmaType ml $ map Left ys
  (envVarName, envVar) <- newDataUpsilon
  let lamBody = (ml, CodeSigmaElim (map fst fvs) envVar e)
  let lamTheta = (ml, DataTheta lamThetaName)
  penv <- gets polEnv
  when (lamThetaName `elem` map fst penv) $
    insPolEnv lamThetaName (envVarName : xs) lamBody
  let fvSigmaIntro =
        ( ml
        , DataSigmaIntro $
          zipWith (curry toDataUpsilon) freeVarNameList (map fst ys))
  return $
    bindLet
      (concat yess)
      (ml, CodeUpIntro (ml, DataSigmaIntro [envExp, fvSigmaIntro, lamTheta]))

makeClosureNonRec ::
     [(Identifier, TermPlus)]
  -> Meta
  -> [Identifier]
  -> CodePlus
  -> WithEnv CodePlus
makeClosureNonRec fvs m xs e = do
  let ml = snd $ obtainInfoMeta m
  let (freeVarNameList, freeVarTypeList) = unzip fvs
  (yess, ys) <- unzip <$> mapM polarize' freeVarTypeList
  envExp <- toSigmaType ml $ map Left ys
  (envVarName, envVar) <- newDataUpsilon
  let lamBody = (ml, CodeSigmaElim (map fst fvs) envVar e)
  let lam = (ml, DataDownIntroPiIntro (envVarName : xs) lamBody)
  let fvSigmaIntro =
        ( ml
        , DataSigmaIntro $
          zipWith (curry toDataUpsilon) freeVarNameList (map fst ys))
  return $
    bindLet
      (concat yess)
      (ml, CodeUpIntro (ml, DataSigmaIntro [envExp, fvSigmaIntro, lam]))

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

exponentImmediate :: WithEnv ValuePlus
exponentImmediate = do
  penv <- gets polEnv
  let thetaName = "EXPONENT.IMMEDIATE"
  let immExp = (Nothing, ValueTheta thetaName)
  case lookup thetaName penv of
    Just _ -> return immExp
    Nothing -> do
      (countVarName, countVar) <- newValueUpsilon
      (immVarName, immVar) <- newValueUpsilon
      let lamBody = (Nothing, CompCopyN countVar immVar)
      insCompEnv thetaName [countVarName, immVarName] lamBody
      return (Nothing, ValueTheta thetaName)

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
  -> [Either ValuePlus (Identifier, ValuePlus)]
  -> WithEnv ValuePlus
exponentSigma lamThetaName ml mxts = do
  penv <- gets polEnv
  let sigmaExp = (ml, ValueTheta lamThetaName)
  case lookup lamThetaName penv of
    Just _ -> return sigmaExp
    Nothing -> do
      xts <- mapM supplyName mxts
      (countVarName, countVar) <- newValueUpsilon
      (sigVarName, sigVar) <- newValueUpsilon
      let appList =
            map
              (\(x, t) ->
                 ( ml
                 , CompPiElimDownElim t [countVar, toValueUpsilon (x, fst t)]))
              xts
      ys <- mapM (const $ newNameWith "var") xts
      let ys' = map toValueUpsilon' ys
      let lamBody =
            ( ml
            , CompSigmaElim
                (map fst xts)
                sigVar
                (bindLetComp (zip ys appList) (ml, CompTransposeN countVar ys')))
      insCompEnv lamThetaName [countVarName, sigVarName] lamBody
      return sigmaExp

bindLetComp :: [(Identifier, CompPlus)] -> CompPlus -> CompPlus
bindLetComp [] cont = cont
bindLetComp ((x, e):xes) cont = do
  let e' = bindLetComp xes cont
  (fst e', CompUpElim x e e')

exponentClosure :: WithEnv ValuePlus
exponentClosure = do
  i <- exponentImmediate
  (typeVarName, typeVar) <- newValueUpsilon
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
  makeClosure'
    []
    name
    m
    [x, y]
    (ml, CodeTheta (ThetaArith op lowType varX varY))

polarizeThetaPrint :: Identifier -> Meta -> WithEnv CodePlus
polarizeThetaPrint name m = do
  let ml = snd $ obtainInfoMeta m
  (x, varX) <- newDataUpsilon
  makeClosure' [] name m [x] (ml, CodeTheta (ThetaPrint varX))

newDataUpsilon :: WithEnv (Identifier, DataPlus)
newDataUpsilon = newDataUpsilon' Nothing

newDataUpsilon' :: Maybe Loc -> WithEnv (Identifier, DataPlus)
newDataUpsilon' ml = do
  x <- newNameWith "arg"
  return (x, (ml, DataUpsilon x))

newValueUpsilon :: WithEnv (Identifier, ValuePlus)
newValueUpsilon = newValueUpsilon' Nothing

newValueUpsilon' :: Maybe Loc -> WithEnv (Identifier, ValuePlus)
newValueUpsilon' ml = do
  x <- newNameWith "arg"
  return (x, (ml, ValueUpsilon x))
