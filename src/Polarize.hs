-- This module "polarizes" a neutral term into a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value. A detailed explanation of Call-By-Push-Value can be found
-- in P. Levy, "Call-by-Push-Value: A Subsuming Paradigm". Ph. D. thesis,
-- Queen Mary College, 2001.
module Polarize
  ( polarize
  , bindLet
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
polarize (m, TermEpsilonIntro l lowType) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataEpsilonIntro l lowType))
polarize (m, TermEpsilonElim (x, _) e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (yts, y) <- polarize' e
  let ml = snd $ obtainInfoMeta m
  return $ bindLet yts (ml, CodeEpsilonElim x y (zip cs es'))
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
  let fvs = obtainFreeVarList xs e
  e' <- polarize e
  makeClosure Nothing fvs m xs e'
polarize (m, TermPiElim e es) = do
  e' <- polarize e
  callClosure m e' es
polarize (m, TermMu (f, t) e) = do
  let ml = snd $ obtainInfoMeta m
  let fvs = obtainFreeVarList [f] e
  let fvs' = map toTermUpsilon fvs
  h <- newNameWith "hole"
  let clsMuType = (MetaTerminal ml, TermPi $ fvs ++ [(h, t)])
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
  cls <- makeClosure (Just f) [] clsMeta (map fst fvs) lamBody'
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
  return $ upElim ml varName e' (ml, CodeUp var)

makeClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e`
  -> Meta -- meta of lambda
  -> [Identifier] -- the `(x1, ..., xn)` in `lam (x1, ..., xn). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
makeClosure mName fvs m xs e = do
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
    Nothing ->
      return $
      bindLet
        (concat yess)
        ( ml
        , CodeUpIntro
            ( ml
            , DataSigmaIntro
                [ envExp
                , fvSigmaIntro
                , (ml, DataDownIntroPiIntro (envVarName : xs) lamBody)
                ]))
    Just lamThetaName -> do
      penv <- gets codeEnv
      when (lamThetaName `elem` map fst penv) $
        insCodeEnv lamThetaName (envVarName : xs) lamBody
      return $
        bindLet
          (concat yess)
          ( ml
          , CodeUpIntro
              ( ml
              , DataSigmaIntro
                  [envExp, fvSigmaIntro, (ml, DataTheta lamThetaName)]))

callClosure :: Meta -> CodePlus -> [TermPlus] -> WithEnv CodePlus
callClosure m e es = do
  (xess, xs) <- unzip <$> mapM polarize' es
  let ml = snd $ obtainInfoMeta m
  (clsVarName, clsVar) <- newDataUpsilon
  (typeVarName, _) <- newDataUpsilon
  (envVarName, envVar) <- newDataUpsilon
  (lamVarName, lamVar) <- newDataUpsilon
  let args = map (\v -> (ml, CodeUpIntro v)) $ envVar : xs
  return $
    upElim
      ml
      clsVarName
      e
      (bindLet
         (concat xess)
         ( ml
         , CodeSigmaElim
               -- ここでのtypevarの取得は実際は省略可。
               -- とはいえ、typeVarはexponentでクロージャをcopyするときに使うので落とすことはできない。
             [typeVarName, envVarName, lamVarName]
             clsVar
             (ml, CodePiElimDownElim lamVar args)))

bindLet :: Binder -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = do
  let e' = bindLet xes cont
  upElim (fst e') x e e'

upElim :: Maybe Loc -> Identifier -> CodePlus -> CodePlus -> CodePlus
upElim ml x e1 e2 =
  (ml, CodePiElimDownElim (ml, DataDownIntroPiIntro [x] e2) [e1])

toSigmaType ::
     Maybe (Int, Int)
  -> [Either DataPlus (Identifier, DataPlus)]
  -> WithEnv DataPlus
toSigmaType ml xps = do
  xps' <- mapM supplyName xps
  return (ml, DataSigma xps')

polarizeTheta :: Meta -> Identifier -> WithEnv CodePlus
polarizeTheta m name@"core.i8.add" = polarizeArith name ArithAdd (int 8) m
polarizeTheta m name@"core.i16.add" = polarizeArith name ArithAdd (int 16) m
polarizeTheta m name@"core.i32.add" = polarizeArith name ArithAdd (int 32) m
polarizeTheta m name@"core.i64.add" = polarizeArith name ArithAdd (int 64) m
polarizeTheta m name@"core.i8.sub" = polarizeArith name ArithSub (int 8) m
polarizeTheta m name@"core.i16.sub" = polarizeArith name ArithSub (int 16) m
polarizeTheta m name@"core.i32.sub" = polarizeArith name ArithSub (int 32) m
polarizeTheta m name@"core.i64.sub" = polarizeArith name ArithSub (int 64) m
polarizeTheta m name@"core.i8.mul" = polarizeArith name ArithMul (int 8) m
polarizeTheta m name@"core.i16.mul" = polarizeArith name ArithMul (int 16) m
polarizeTheta m name@"core.i32.mul" = polarizeArith name ArithMul (int 32) m
polarizeTheta m name@"core.i64.mul" = polarizeArith name ArithMul (int 64) m
polarizeTheta m name@"core.i8.div" = polarizeArith name ArithDiv (int 8) m
polarizeTheta m name@"core.i16.div" = polarizeArith name ArithDiv (int 16) m
polarizeTheta m name@"core.i32.div" = polarizeArith name ArithDiv (int 32) m
polarizeTheta m name@"core.i64.div" = polarizeArith name ArithDiv (int 64) m
polarizeTheta m name@"core.f32.add" = polarizeArith name ArithAdd (float 32) m
polarizeTheta m name@"core.f64.add" = polarizeArith name ArithAdd (float 64) m
polarizeTheta m name@"core.f32.sub" = polarizeArith name ArithSub (float 32) m
polarizeTheta m name@"core.f64.sub" = polarizeArith name ArithSub (float 64) m
polarizeTheta m name@"core.f32.mul" = polarizeArith name ArithMul (float 32) m
polarizeTheta m name@"core.f64.mul" = polarizeArith name ArithMul (float 64) m
polarizeTheta m name@"core.f32.div" = polarizeArith name ArithDiv (float 32) m
polarizeTheta m name@"core.f64.div" = polarizeArith name ArithDiv (float 64) m
polarizeTheta m name@"core.print.i64" = polarizePrint name m
polarizeTheta _ _ = throwError "polarize.theta"

int :: Int -> LowType
int = LowTypeSignedInt

float :: Int -> LowType
float = LowTypeFloat

polarizeArith :: Identifier -> Arith -> LowType -> Meta -> WithEnv CodePlus
polarizeArith name op lowType m = do
  let ml = snd $ obtainInfoMeta m
  (x, varX) <- newDataUpsilon
  (y, varY) <- newDataUpsilon
  makeClosure
    (Just name)
    []
    m
    [x, y]
    (ml, CodeTheta (ThetaArith op lowType varX varY))

polarizePrint :: Identifier -> Meta -> WithEnv CodePlus
polarizePrint name m = do
  let ml = snd $ obtainInfoMeta m
  (x, varX) <- newDataUpsilon
  makeClosure (Just name) [] m [x] (ml, CodeTheta (ThetaPrint varX))

newDataUpsilon :: WithEnv (Identifier, DataPlus)
newDataUpsilon = newDataUpsilon' Nothing

newDataUpsilon' :: Maybe Loc -> WithEnv (Identifier, DataPlus)
newDataUpsilon' ml = do
  x <- newNameWith "arg"
  return (x, (ml, DataUpsilon x))
