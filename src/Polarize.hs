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

import Control.Monad.Except
import Control.Monad.State
import Prelude hiding (pi)

import Data.Basic
import Data.Code
import Data.Env
import Data.Term

polarize :: TermPlus -> WithEnv CodePlus
polarize (m, TermTau) = do
  let ml = snd $ obtainInfoMeta m
  v <- exponentImmediate ml
  return (ml, CodeUpIntro v)
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataUpsilon x))
polarize (m, TermEpsilon _) = do
  let ml = snd $ obtainInfoMeta m
  v <- exponentImmediate ml
  return (ml, CodeUpIntro v)
polarize (m, TermEpsilonIntro l lowType) = do
  let ml = snd $ obtainInfoMeta m
  return (ml, CodeUpIntro (ml, DataEpsilonIntro l lowType))
polarize (m, TermEpsilonElim (x, _) e bs) = do
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (yts, y) <- polarize' e
  let ml = snd $ obtainInfoMeta m
  return $ bindLet yts (ml, CodeEpsilonElim x y (zip cs es'))
polarize (m, TermPi _) = do
  let ml = snd $ obtainInfoMeta m
  tau <- exponentImmediate ml
  (envVarName, envVar) <- newDataUpsilon
  let retTau = (ml, CodeUpIntro tau)
  let retEnvVar = (ml, CodeUpIntro envVar)
  closureType <-
    exponentSigma
      "CLS"
      ml
      [Right (envVarName, retTau), Left retEnvVar, Left retTau]
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
  let (nameList, _, typeList) = unzip3 $ obtainFreeVarList [f] e
  let fvs = zip nameList typeList
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
  cls <- makeClosure (Just f) [] clsMeta nameList lamBody'
  -- cls <- makeClosure (Just f) [] clsMeta (map fst fvs) lamBody'
  callClosure m cls fvs'

-- ここを適切に型をたどるように変更すればsigmaをすべてclosedにできる
-- varTermPlusのほうを修正する感じか。……termplusのほうなのか。
obtainFreeVarList ::
     [Identifier] -> TermPlus -> [(Identifier, Maybe Loc, TermPlus)]
obtainFreeVarList xs e = do
  filter (\(x, _, _) -> x `notElem` xs) $ varTermPlus e

type Binder = [(Identifier, CodePlus)]

polarize' :: TermPlus -> WithEnv (Binder, DataPlus)
polarize' e@(m, _) = do
  e' <- polarize e
  (varName, var) <- newDataUpsilon' $ snd $ obtainInfoMeta m
  return ([(varName, e')], var)

makeClosure ::
     Maybe Identifier -- the name of newly created closure
  -> [(Identifier, Maybe Loc, TermPlus)] -- list of free variables in `lam (x1, ..., xn). e`
  -> Meta -- meta of lambda
  -> [Identifier] -- the `(x1, ..., xn)` in `lam (x1, ..., xn). e`
  -> CodePlus -- the `e` in `lam (x1, ..., xn). e`
  -> WithEnv CodePlus
makeClosure mName fvs m xs e = do
  let ml = snd $ obtainInfoMeta m
  let (freeVarNameList, locList, freeVarTypeList) = unzip3 fvs
  negTypeList <- mapM polarize freeVarTypeList
  expName <- newNameWith "exp"
  envExp <- exponentSigma expName ml $ map Left negTypeList
  (envVarName, envVar) <- newDataUpsilon
  let lamBody = (ml, CodeSigmaElim freeVarNameList envVar e)
  let fvSigmaIntro =
        ( ml
        , DataSigmaIntro $ zipWith (curry toDataUpsilon) freeVarNameList locList)
  name <-
    case mName of
      Just lamThetaName -> return lamThetaName
      Nothing -> newNameWith "cls"
  penv <- gets codeEnv
  when (name `elem` map fst penv) $ insCodeEnv name (envVarName : xs) lamBody
  return $
    ( ml
    , CodeUpIntro
        (ml, DataSigmaIntro [envExp, fvSigmaIntro, (ml, DataTheta name)]))

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
    ( ml
    , CodeUpElim
        clsVarName -- このclsVarはlinearに使用されるのでexponentの挿入は不要。
        e
        (bindLet
           (concat xess)
           ( ml
           , CodeSigmaElim
               -- ここでのtypevarの取得は実際は省略可。
               -- とはいえ、typeVarはexponentでクロージャをcopyするときに使うので落とすことはできない。
               -- exponentについて。このsigmaElimによっては、typeVarNameはただで捨てられるから放置でよく、
               -- かつenvVarとlamVarはlinearに使用されているから放置でよく、
               -- したがってexponent関連の処理をおこなう必要はない。
               [typeVarName, envVarName, lamVarName]
               clsVar
               (ml, CodePiElimDownElim lamVar args))))

bindLet :: Binder -> CodePlus -> CodePlus
bindLet [] cont = cont
bindLet ((x, e):xes) cont = do
  let e' = bindLet xes cont
  -- TODO: xの使用回数にあわせてここでxについてのexponentをおこなう必要がある。
  (fst e', CodeUpElim x e e')

-- imm n v ~> (v, ..., v) (n times)
-- ここでは「変数はlinearに使用されなければならない」という制約ははたらかない。
-- exponentがprimitiveとしてあるような言語において変数がlinearに使用されている、ってのがポイントなので。
-- exponentの中身は変数の仕様についての治外法権。
exponentImmediate :: Maybe Loc -> WithEnv DataPlus
exponentImmediate ml = do
  cenv <- gets codeEnv
  let thetaName = "EXPONENT.IMMEDIATE"
  let immExp = (ml, DataTheta thetaName)
  case lookup thetaName cenv of
    Just _ -> return immExp
    Nothing -> do
      (countVarName, countVar) <- newDataUpsilon
      (immVarName, immVar) <- newDataUpsilon
      let lamBody = (ml, CodeCopyN countVar immVar)
      insCodeEnv thetaName [countVarName, immVarName] lamBody
      return (ml, DataTheta thetaName)

-- exponentSigma [y1, return t1, ..., yn, return tn]  (where yi : ti)  ~>
--   lam (m, z).
--     let (y1, ..., yn) := z in
--     bind f1 = return t1 in
--     bind ys1 = f1 @ (m, y1) in
--     ...
--     bind fn = return tn in
--     bind ysn = fn @ (m, yn) in -- ここまではコードとしてstaticに書ける
--     let (ys1-1, ..., ys1-m) := ys1 in -- ここでm-elimが必要になる。
--     ...
--     let (ysn-1, ..., ysn-m) := ysn in
--     ((ys1-1, ..., ysn-1), ..., (ys1-m, ..., ysn-m))
--
-- (Note that Sigma (y1 : t1, ..., yn : tn) must be closed.)
exponentSigma ::
     Identifier
  -> Maybe Loc
  -> [Either CodePlus (Identifier, CodePlus)]
  -> WithEnv DataPlus
exponentSigma lamThetaName ml mxes = do
  cenv <- gets codeEnv
  let sigmaExp = (ml, DataTheta lamThetaName)
  case lookup lamThetaName cenv of
    Just _ -> return sigmaExp
    Nothing -> do
      xes <- mapM supplyName mxes
      (countVarName, countVar) <- newDataUpsilon
      (sigVarName, sigVar) <- newDataUpsilon
      appList <- forM xes $ \(x, e) -> toExponentApp countVar ml x e
      ys <- mapM (const $ newNameWith "var") xes
      let ys' = map toDataUpsilon' ys
      let lamBody =
            ( ml
            , CodeSigmaElim
                (map fst xes)
                sigVar
                (bindLet (zip ys appList) (ml, CodeTransposeN countVar ys')))
      insCodeEnv lamThetaName [countVarName, sigVarName] lamBody
      return sigmaExp

toExponentApp ::
     (CodeMeta, Data) -> Maybe Loc -> Identifier -> CodePlus -> WithEnv CodePlus
toExponentApp countVar ml x e = do
  let ds = [countVar, toDataUpsilon (x, fst e)]
  let ds' = map (\(ml', v) -> (ml', CodeUpIntro (ml', v))) ds
  exponentName <- newNameWith "ty"
  return
    ( ml
    , CodeUpElim
        exponentName
        e
        (ml, CodePiElimDownElim (ml, DataUpsilon exponentName) ds'))

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
