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
import           Data.Env
import           Data.Term
import           Data.WeakCode
import           Reduce.WeakCode

polarize :: TermPlus -> WithEnv WeakCodePlus
polarize (m, TermTau) = do
  (u, ml) <- polarizeMeta m
  return (negMeta (up u ml) ml, WeakCodeUpIntro (posMeta u ml, WeakDataTau))
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (u, ml) <- polarizeMeta m
  return
    (negMeta (up u ml) ml, WeakCodeUpIntro (posMeta u ml, WeakDataUpsilon x))
polarize (m, TermEpsilon x) = do
  (u, ml) <- polarizeMeta m
  return
    (negMeta (up u ml) ml, WeakCodeUpIntro (posMeta u ml, WeakDataEpsilon x))
polarize (m, TermEpsilonIntro l) = do
  (u, ml) <- polarizeMeta m
  return
    ( negMeta (up u ml) ml
    , WeakCodeUpIntro (posMeta u ml, WeakDataEpsilonIntro l))
polarize (m, TermEpsilonElim (x, t) e bs) = do
  (u, ml) <- polarizeMeta m
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (y, ye) <- polarize' e
  (z, zt) <- polarize' t
  bindLet
    [ye, zt]
    (negMeta (up u ml) ml, WeakCodeEpsilonElim (x, z) y (zip cs es'))
polarize (m, TermPi xts t) = do
  (u, ml) <- polarizeMeta m
  p <- polarize t >>= reduceWeakCodePlus >>= extract
  (xs', xts', xs) <- polarizePlus xts
  let negMetaMeta = WeakCodeMetaTerminal ml
  let z' = (negMetaMeta, WeakCodeUp p)
  bindLet
    xts'
    ( negMeta (up u ml) ml
    , WeakCodeUpIntro
        (posMeta u ml, WeakDataDown (negMetaMeta, WeakCodePi (zip xs xs') z')))
polarize (m, TermPiIntro xts e) = makeClosure m xts e
  -- (d, ml) <- polarizeMeta m
  -- pi <- extractFromDown d
  -- (ys', yts', xs) <- polarizePlus xts
  -- e' <- polarize e
  -- -- makeClosure m xps e'
  -- let vs = varWeakCodePlus e'
  -- bindLet
  --   yts'
  --   ( negMeta (up d ml) ml
  --   , WeakCodeUpIntro
  --       ( posMeta d ml
  --       , WeakDataDownIntro (negMeta pi ml, WeakCodePiIntro (zip xs ys') e')))
polarize (m, TermPiElim e es) = callClosure m e es
  -- (t, ml2) <- polarizeMeta m
  -- (f', fe') <- polarize' e
  -- (xs', xes') <- unzip <$> mapM polarize' es
  -- (tpi, tml) <- polarizeMeta me
  -- pi <- extractFromDown tpi
  -- bindLet
  --   (fe' : xes')
  --   ( negMeta (up t ml2) ml2
  --   , WeakCodePiElim (negMeta pi tml, WeakCodeDownElim f') xs')
polarize (m, TermSigma xts t) = do
  (u, ml) <- polarizeMeta m
  p <- polarize t >>= reduceWeakCodePlus >>= extract
  (ys', yts', xs) <- polarizePlus xts
  bindLet
    yts'
    ( negMeta (up u ml) ml
    , WeakCodeUpIntro (posMeta u ml, WeakDataSigma (zip xs ys') p))
polarize (m, TermSigmaIntro es) = do
  (u, ml) <- polarizeMeta m
  (xs, xes) <- unzip <$> mapM polarize' es
  bindLet
    xes
    ( negMeta (up u ml) ml
    , WeakCodeUpIntro (posMeta u ml, WeakDataSigmaIntro xs))
polarize (m, TermSigmaElim xts e1 e2) = do
  (u, ml) <- polarizeMeta m
  (z', ze1') <- polarize' e1
  (ys', yts', xs) <- polarizePlus xts
  e2' <- polarize e2
  bindLet
    (ze1' : yts')
    (negMeta (up u ml) ml, WeakCodeSigmaElim (zip xs ys') z' e2')
polarize (m, TermMu (x, t) e) = do
  e' <- polarize e
  let fvs = varWeakCodePlus e'
  lamVar <- newNameWith "cls"
  envName <- newNameWith "env"
  -- let (x1, ..., xn) := env in
  -- bind x := (down-elim z) @ (x1, ..., xn) in
  -- e
  let lamBody =
        ( undefined
        , WeakCodeSigmaElim
            fvs
            (undefined, WeakDataUpsilon envName)
            ( undefined
            , WeakCodeUpElim
                (x, undefined)
                ( undefined
                , WeakCodePiElimDownElim
                    (undefined, WeakDataUpsilon lamVar)
                    (map toVar fvs))
                e'))
  insPolEnv lamVar ((envName, undefined) : undefined) lamBody
  return
    ( undefined
    , WeakCodePiElimDownElim (undefined, WeakDataUpsilon lamVar) (map toVar fvs))
  -- mu . e ~> (down-elim f) @ fvs
  -- (u, ml) <- polarizeMeta m
  -- (y', yt') <- polarize' t
  -- (k', kt') <- polarize' e
  -- inner <- bindLet [kt'] (negMeta (up u ml) ml, WeakCodeDownElim k')
  -- bindLet [yt'] (negMeta (up u ml) ml, WeakCodeMu (x, y') inner)

makeClosure ::
     Meta -> [(Identifier, TermPlus)] -> TermPlus -> WithEnv WeakCodePlus
makeClosure m xts e = do
  (d, ml) <- polarizeMeta m
  pi <- extractFromDown d
  -- (ys', yts', xs) <- polarizePlus xts
  xps <- polarizePlus' xts
  e' <- polarize e
  let vs = varWeakCodePlus e'
  lamVar <- newNameWith "cls"
  envName <- newNameWith "env"
  let lamBody =
        ( undefined
        , WeakCodeSigmaElim vs (undefined, WeakDataUpsilon envName) e')
  -- lamVar == thunk (lam (envName, x1, ..., xn) lamBody)
  insPolEnv lamVar ((envName, undefined) : xps) lamBody
  let fvEnv = (undefined, WeakDataSigmaIntro $ map toVar vs)
  return
    ( undefined
    , WeakCodeUpIntro
        ( undefined
        , WeakDataSigmaIntro [(undefined, WeakDataUpsilon lamVar), fvEnv]))
  -- bindLet
  --   yts'
  --   ( negMeta (up d ml) ml
  --   , WeakCodeUpIntro
  --       ( posMeta d ml
  --       , WeakDataDownIntro (negMeta pi ml, WeakCodePiIntro (zip xs ys') e')))
  -- let lamBody = WeakCodeSigmaElim fvs (PosUpsilon envName) e
  -- -- lamVar == thunk (lam (envName, x1, ..., xn) lamBody)
  -- insPolEnv lamVar (envName : xs) lamBody
  -- let fvEnv = PosSigmaIntro $ map PosUpsilon fvs
  -- return $ WeakCodeUpIntro $ PosSigmaIntro [PosConst lamVar, fvEnv]

callClosure :: Meta -> TermPlus -> [TermPlus] -> WithEnv WeakCodePlus
callClosure m e es = do
  e' <- polarize e
  es' <- mapM polarize es
  argVarNameList <- mapM (const $ newNameWith "arg") es
  clsVarName <- newNameWith "fun"
  thunkLamVarName <- newNameWith "down.elim.cls"
  envVarName <- newNameWith "down.elim.env"
  foo <-
    bindLet
      (zip argVarNameList es')
      ( undefined
      , WeakCodeSigmaElim
          [(thunkLamVarName, undefined), (envVarName, undefined)]
          (undefined, WeakDataUpsilon clsVarName)
          ( undefined
          , WeakCodePiElimDownElim
              (undefined, WeakDataUpsilon thunkLamVarName)
              ((undefined, WeakDataUpsilon envVarName) :
               map undefined argVarNameList)))
  return (undefined, WeakCodeUpElim (clsVarName, undefined) e' foo)
          -- ( undefined
          -- , WeakCodeSigmaElim
          --     [thunkLamVarName, envVarName]
          --     (PosUpsilon clsVarName) $
          --   WeakCodePiElimDownElim
          --     (PosUpsilon thunkLamVarName)
          --     (PosUpsilon envVarName : map PosUpsilon argVarNameList))
  -- return $
  --   WeakCodeUpElim clsVarName e $
  --   bindLet (zip argVarNameList es) $
  --   WeakCodeSigmaElim [thunkLamVarName, envVarName] (PosUpsilon clsVarName) $
  --   WeakCodePiElimDownElim
  --     (PosUpsilon thunkLamVarName)
  --     (PosUpsilon envVarName : map PosUpsilon argVarNameList)

--   argVarNameList <- mapM (const $ newNameWith "arg") es
--   clsVarName <- newNameWith "fun"
--   thunkLamVarName <- newNameWith "down.elim.cls"
--   envVarName <- newNameWith "down.elim.env"
--   undefined
toVar :: (Identifier, WeakDataPlus) -> WeakDataPlus
toVar = undefined

polarize' :: TermPlus -> WithEnv (WeakDataPlus, (Identifier, WeakCodePlus))
polarize' e@(m, _) = do
  e' <- polarize e
  (p, ml) <- polarizeMeta m
  x <- newNameWith "var"
  return ((posMeta p ml, WeakDataUpsilon x), (x, e'))

bindLet :: [(Identifier, WeakCodePlus)] -> WeakCodePlus -> WithEnv WeakCodePlus
bindLet [] cont = return cont
bindLet ((x, e@(m, _)):xes) cont = do
  e' <- bindLet xes cont
  let (typeOfCont, ml) = obtainInfoWeakCodeMeta $ fst e'
  p <- extract $ fst $ obtainInfoWeakCodeMeta m
  -- kleisli extension (i.e. dependent up-elimination)
  let ke = (fst typeOfCont, WeakCodeUpElim (x, p) e typeOfCont)
  return (negMeta ke ml, WeakCodeUpElim (x, p) e e')

obtainInfoMeta :: Meta -> (TermPlus, Maybe (Int, Int))
obtainInfoMeta (MetaTerminal ml)      = ((MetaTerminal ml, TermTau), ml)
obtainInfoMeta (MetaNonTerminal t ml) = (t, ml)

polarizePlus ::
     [(a, TermPlus)]
  -> WithEnv ([WeakDataPlus], [(Identifier, WeakCodePlus)], [a])
polarizePlus xts = do
  let (xs, ts) = unzip xts
  (ys', yts') <- unzip <$> mapM polarize' ts
  return (ys', yts', xs)

polarizePlus' :: [(a, TermPlus)] -> WithEnv [(a, WeakDataPlus)]
polarizePlus' xts = do
  let (xs, ts) = unzip xts
  ps <- mapM (polarize >=> reduceWeakCodePlus >=> extract) ts
  return $ zip xs ps
  -- (ys', yts') <- unzip <$> mapM polarize' ts
  -- return (ys', yts', xs)

polarizeMeta :: Meta -> WithEnv (WeakDataPlus, Maybe (Int, Int))
polarizeMeta m = do
  let (t, ml) = obtainInfoMeta m
  d <- polarize t >>= reduceWeakCodePlus >>= extract
  return (d, ml)

extract :: WeakCodePlus -> WithEnv WeakDataPlus
extract e =
  case e of
    (_, WeakCodeUpIntro d) -> return d
    _                      -> throwError "extract"

extractFromDown :: WeakDataPlus -> WithEnv WeakCodePlus
extractFromDown e =
  case e of
    (_, WeakDataDown d) -> return d
    _                   -> throwError "extract"

posMeta :: WeakDataPlus -> Maybe (Int, Int) -> WeakDataMeta
posMeta = WeakDataMetaNonTerminal

negMeta :: WeakCodePlus -> Maybe (Int, Int) -> WeakCodeMeta
negMeta = WeakCodeMetaNonTerminal

up :: WeakDataPlus -> Maybe (Int, Int) -> WeakCodePlus
up u ml = (WeakCodeMetaTerminal ml, WeakCodeUp u)

-- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv WeakCodePlus
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

polarizeThetaArith :: Arith -> Meta -> WithEnv WeakCodePlus
polarizeThetaArith op m = do
  (upT, ml) <- polarizeMeta m
  case upT of
    d@(_, WeakDataDown (_, WeakCodePi _ (_, WeakCodeUp int))) -> do
      (x, varX) <- varOfType int
      (y, varY) <- varOfType int
      return
        ( negMeta (up d ml) ml
        , WeakCodeUpIntro
            ( posMeta d ml
            , WeakDataDownIntroPiIntro
                [(x, int), (y, int)]
                ( negMeta (up int ml) ml
                , WeakCodeTheta (WeakThetaArith op varX varY))))
    _ -> throwError "polarize.theta.arith"

polarizeThetaPrint :: Meta -> WithEnv WeakCodePlus
polarizeThetaPrint m = do
  (upT, ml) <- polarizeMeta m
  case upT of
    d@(_, WeakDataDown (_, WeakCodePi [(_, int)] cod)) -> do
      (x, varX) <- varOfType int
      return
        ( negMeta (up d ml) ml
        , WeakCodeUpIntro
            ( posMeta d ml
            , WeakDataDownIntroPiIntro
                [(x, int)]
                (negMeta cod ml, WeakCodeTheta (WeakThetaPrint varX))))
    _ -> throwError "polarize.theta.print"

varOfType :: WeakDataPlus -> WithEnv (Identifier, WeakDataPlus)
varOfType t = do
  x <- newNameWith "arg"
  return (x, (posMeta t Nothing, WeakDataUpsilon x))
