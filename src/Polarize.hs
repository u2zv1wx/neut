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
polarize (m, TermPiIntro xts e) = makeClosure m xts e
polarize (m, TermPiElim e es) = callClosure m e es
polarize (m, TermSigma xts t) = do
  (u, ml) <- polarizeMeta m
  p <- polarize t >>= reduceCodePlus >>= extract
  (ys', yts', xs) <- polarizePlus xts
  bindLet
    yts'
    (negMeta (up u ml) ml, CodeUpIntro (posMeta u ml, DataSigma (zip xs ys') p))
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
polarize (m, TermMu (x, t) e) = do
  e' <- polarize e
  let fvs = varCodePlus e'
  lamVar <- newNameWith "cls"
  envName <- newNameWith "env"
  let lamBody =
        ( undefined
        , CodeSigmaElim
            fvs
            (undefined, DataUpsilon envName)
            ( undefined
            , CodeUpElim
                (x, undefined)
                ( undefined
                , CodePiElimDownElim
                    (undefined, DataUpsilon lamVar)
                    (map toVar fvs))
                e'))
  insPolEnv lamVar ((envName, undefined) : undefined) lamBody
  return
    ( undefined
    , CodePiElimDownElim (undefined, DataTheta lamVar) (map toVar fvs))
  -- mu . e ~> (down-elim f) @ fvs
  -- (u, ml) <- polarizeMeta m
  -- (y', yt') <- polarize' t
  -- (k', kt') <- polarize' e
  -- inner <- bindLet [kt'] (negMeta (up u ml) ml, CodeDownElim k')
  -- bindLet [yt'] (negMeta (up u ml) ml, CodeMu (x, y') inner)

makeClosure :: Meta -> [(Identifier, TermPlus)] -> TermPlus -> WithEnv CodePlus
makeClosure m xts e = do
  (d, ml) <- polarizeMeta m
  pi <- extractFromDown d
  -- (ys', yts', xs) <- polarizePlus xts
  xps <- polarizePlus' xts
  e' <- polarize e
  let vs = varCodePlus e'
  lamVar <- newNameWith "cls"
  envName <- newNameWith "env"
  let lamBody =
        (undefined, CodeSigmaElim vs (undefined, DataUpsilon envName) e')
  -- lamVar == thunk (lam (envName, x1, ..., xn) lamBody)
  insPolEnv lamVar ((envName, undefined) : xps) lamBody
  let fvEnv = (undefined, DataSigmaIntro $ map toVar vs)
  return
    ( undefined
    , CodeUpIntro
        (undefined, DataSigmaIntro [(undefined, DataTheta lamVar), fvEnv]))
  -- bindLet
  --   yts'
  --   ( negMeta (up d ml) ml
  --   , CodeUpIntro
  --       ( posMeta d ml
  --       , DataDownIntro (negMeta pi ml, CodePiIntro (zip xs ys') e')))
  -- let lamBody = CodeSigmaElim fvs (PosUpsilon envName) e
  -- -- lamVar == thunk (lam (envName, x1, ..., xn) lamBody)
  -- insPolEnv lamVar (envName : xs) lamBody
  -- let fvEnv = PosSigmaIntro $ map PosUpsilon fvs
  -- return $ CodeUpIntro $ PosSigmaIntro [PosConst lamVar, fvEnv]

callClosure :: Meta -> TermPlus -> [TermPlus] -> WithEnv CodePlus
callClosure m e es = do
  e' <- polarize e
  es' <- mapM polarize es
  argVarNameList <- mapM (const $ newNameWith "arg") es
  clsVarName <- newNameWith "fun"
  thunkLamVarName <- newNameWith "down.elim.cls"
  envVarName <- newNameWith "down.elim.env"
  cont <-
    bindLet
      (zip argVarNameList es')
      ( undefined
      , CodeSigmaElim
          [(thunkLamVarName, undefined), (envVarName, undefined)]
          (undefined, DataUpsilon clsVarName)
          ( undefined
          , CodePiElimDownElim
              (undefined, DataUpsilon thunkLamVarName)
              ((undefined, DataUpsilon envVarName) :
               map undefined argVarNameList)))
  return (undefined, CodeUpElim (clsVarName, undefined) e' cont)
          -- ( undefined
          -- , CodeSigmaElim
          --     [thunkLamVarName, envVarName]
          --     (PosUpsilon clsVarName) $
          --   CodePiElimDownElim
          --     (PosUpsilon thunkLamVarName)
          --     (PosUpsilon envVarName : map PosUpsilon argVarNameList))
  -- return $
  --   CodeUpElim clsVarName e $
  --   bindLet (zip argVarNameList es) $
  --   CodeSigmaElim [thunkLamVarName, envVarName] (PosUpsilon clsVarName) $
  --   CodePiElimDownElim
  --     (PosUpsilon thunkLamVarName)
  --     (PosUpsilon envVarName : map PosUpsilon argVarNameList)

toVar :: (Identifier, DataPlus) -> DataPlus
toVar = undefined

polarize' :: TermPlus -> WithEnv (DataPlus, (Identifier, CodePlus))
polarize' e@(m, _) = do
  e' <- polarize e
  (p, ml) <- polarizeMeta m
  x <- newNameWith "var"
  return ((posMeta p ml, DataUpsilon x), (x, e'))

bindLet :: [(Identifier, CodePlus)] -> CodePlus -> WithEnv CodePlus
bindLet [] cont = return cont
bindLet ((x, e@(m, _)):xes) cont = do
  e' <- bindLet xes cont
  let (typeOfCont, ml) = obtainInfoCodeMeta $ fst e'
  p <- extract $ fst $ obtainInfoCodeMeta m
  -- kleisli extension (i.e. dependent up-elimination)
  let ke = (fst typeOfCont, CodeUpElim (x, p) e typeOfCont)
  return (negMeta ke ml, CodeUpElim (x, p) e e')

obtainInfoMeta :: Meta -> (TermPlus, Maybe (Int, Int))
obtainInfoMeta (MetaTerminal ml)      = ((MetaTerminal ml, TermTau), ml)
obtainInfoMeta (MetaNonTerminal t ml) = (t, ml)

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

extractFromDown :: DataPlus -> WithEnv CodePlus
extractFromDown e =
  case e of
    (_, DataDown d) -> return d
    _               -> throwError "extract"

posMeta :: DataPlus -> Maybe (Int, Int) -> DataMeta
posMeta = DataMetaNonTerminal

negMeta :: CodePlus -> Maybe (Int, Int) -> CodeMeta
negMeta = CodeMetaNonTerminal

up :: DataPlus -> Maybe (Int, Int) -> CodePlus
up u ml = (CodeMetaTerminal ml, CodeUp u)

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
      (x, varX) <- varOfType int
      (y, varY) <- varOfType int
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
      (x, varX) <- varOfType int
      return
        ( negMeta (up d ml) ml
        , CodeUpIntro
            ( posMeta d ml
            , DataDownIntroPiIntro
                [(x, int)]
                (negMeta cod ml, CodeTheta (ThetaPrint varX))))
    _ -> throwError "polarize.theta.print"

varOfType :: DataPlus -> WithEnv (Identifier, DataPlus)
varOfType t = do
  x <- newNameWith "arg"
  return (x, (posMeta t Nothing, DataUpsilon x))
