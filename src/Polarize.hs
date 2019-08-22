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
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return (negMeta (up u ml) ml, WeakCodeUpIntro (posMeta u ml, WeakDataTau))
    _ -> throwError "polarize.tau"
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return
        ( negMeta (up u ml) ml
        , WeakCodeUpIntro (posMeta u ml, WeakDataUpsilon x))
    _ -> throwError "polarize.upsilon"
polarize (m, TermEpsilon x) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return
        ( negMeta (up u ml) ml
        , WeakCodeUpIntro (posMeta u ml, WeakDataEpsilon x))
    _ -> throwError "polarize.epsilon"
polarize (m, TermEpsilonIntro l) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return
        ( negMeta (up u ml) ml
        , WeakCodeUpIntro (posMeta u ml, WeakDataEpsilonIntro l))
    _ -> throwError "polarize.epsilon-intro"
polarize (m, TermEpsilonElim (x, t) e bs) = do
  (t1, ml) <- polarizeMeta m
  case t1 of
    (_, WeakCodeUpIntro u) -> do
      let (cs, es) = unzip bs
      es' <- mapM polarize es
      (y, ye) <- polarize' e
      (z, zt) <- polarize' t
      bindLet
        [ye, zt]
        (negMeta (up u ml) ml, WeakCodeEpsilonElim (x, z) y (zip cs es'))
    _ -> throwError "polarize.epsilon-elim"
polarize (m, TermPi xts t) = do
  (tm, ml) <- polarizeMeta m
  t' <- polarize t >>= reduceWeakCodePlus
  case (tm, t') of
    ((_, WeakCodeUpIntro u), (_, WeakCodeUpIntro p)) -> do
      (xs', xts', xs) <- polarizePlus xts
      let negMetaMeta = WeakCodeMetaTerminal ml
      let z' = (negMetaMeta, WeakCodeUp p)
      bindLet
        xts'
        ( negMeta (up u ml) ml
        , WeakCodeUpIntro
            ( posMeta u ml
            , WeakDataDown (negMetaMeta, WeakCodePi (zip xs xs') z')))
    _ -> throwError "polarize.pi"
polarize (m, TermPiIntro xts e) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro d) -> do
      (ys', yts', xs) <- polarizePlus xts
      e' <- polarize e
      bindLet
        yts'
        ( negMeta (up d ml) ml
        , WeakCodeUpIntro
            (posMeta d ml, WeakDataDownIntroPiIntro (zip xs ys') e'))
    _ -> throwError "polarize.pi-intro"
polarize (m, TermPiElim e es) = do
  (t2, ml2) <- polarizeMeta m
  case t2 of
    (_, WeakCodeUpIntro t) -> do
      (f', fe') <- polarize' e
      (xs', xes') <- unzip <$> mapM polarize' es
      bindLet
        (fe' : xes')
        (negMeta (up t ml2) ml2, WeakCodePiElimDownElim f' xs')
    _ -> throwError "polarize.pi-elim"
polarize (m, TermSigma xts t) = do
  (tm, ml) <- polarizeMeta m
  t' <- polarize t >>= reduceWeakCodePlus
  case (tm, t') of
    ((_, WeakCodeUpIntro u), (_, WeakCodeUpIntro p)) -> do
      (ys', yts', xs) <- polarizePlus xts
      bindLet
        yts'
        ( negMeta (up u ml) ml
        , WeakCodeUpIntro (posMeta u ml, WeakDataSigma (zip xs ys') p))
    _ -> throwError "polarize.epsilon-intro"
polarize (m, TermSigmaIntro es) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) -> do
      (xs, xes) <- unzip <$> mapM polarize' es
      bindLet
        xes
        ( negMeta (up u ml) ml
        , WeakCodeUpIntro (posMeta u ml, WeakDataSigmaIntro xs))
    _ -> throwError "polarize.sigma-intro"
polarize (m, TermSigmaElim xts e1 e2) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) -> do
      (z', ze1') <- polarize' e1
      (ys', yts', xs) <- polarizePlus xts
      e2' <- polarize e2
      bindLet
        (ze1' : yts')
        (negMeta (up u ml) ml, WeakCodeSigmaElim (zip xs ys') z' e2')
    _ -> throwError "polarize.sigma-elim"
polarize (m, TermMu (x, t) e) = do
  (t1, ml) <- polarizeMeta m
  case t1 of
    (_, WeakCodeUpIntro u) -> do
      (y', yt') <- polarize' t
      (k', kt') <- polarize' e
      inner <-
        bindLet [kt'] (negMeta (up u ml) ml, WeakCodePiElimDownElim k' [])
      bindLet [yt'] (negMeta (up u ml) ml, WeakCodeMu (x, y') inner)
    _ -> throwError "polarize.mu"

polarize' :: TermPlus -> WithEnv (WeakDataPlus, (Identifier, WeakCodePlus))
polarize' e@(m, _) = do
  e' <- polarize e
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro p) -> do
      x <- newNameWith "var"
      return ((posMeta p ml, WeakDataUpsilon x), (x, e'))
    _ -> throwError "polarize'"

bindLet :: [(Identifier, WeakCodePlus)] -> WeakCodePlus -> WithEnv WeakCodePlus
bindLet [] cont = return cont
bindLet ((x, e@(m, _)):xes) cont = do
  e' <- bindLet xes cont
  let (typeOfCont, ml) = obtainInfoWeakCodeMeta $ fst e'
  let (t2, _) = obtainInfoWeakCodeMeta m
  case t2 of
    (_, WeakCodeUp p) -> do
      let ke = (fst typeOfCont, WeakCodeUpElim (x, p) e typeOfCont)
      -- "ke" here stands for "Kleisli Extension" (i.e. dependent up-elimination).
      -- Notes on this concept can be found in Section 16.3 of Levy's paper, and also in
      -- M. Vákár, "An Effectful Treatment of Dependent Types", arXiv:1603.04298, 2016.
      -- Vákár's approarch:
      --   type of `e2` : N {z := thunk (return x)}
      --   type of `bind x := e1 in e2` N {z := thunk e}
      -- Our approach:
      --   type of `e2` : N
      --   type of `bind x := e1 in e2` : bind x := e1 in N
      return (negMeta ke ml, WeakCodeUpElim (x, p) e e')
    _ -> throwError "bindLet"

obtainInfoMeta :: Meta -> (TermPlus, Maybe (Int, Int))
obtainInfoMeta (MetaTerminal ml)      = ((MetaTerminal ml, TermTau), ml)
obtainInfoMeta (MetaNonTerminal t ml) = (t, ml)

obtainInfoWeakCodeMeta :: WeakCodeMeta -> (WeakCodePlus, Maybe (Int, Int))
obtainInfoWeakCodeMeta (WeakCodeMetaTerminal ml) =
  ((WeakCodeMetaTerminal ml, WeakCodeTau), ml)
obtainInfoWeakCodeMeta (WeakCodeMetaNonTerminal t ml) = (t, ml)

polarizePlus ::
     [(a, TermPlus)]
  -> WithEnv ([WeakDataPlus], [(Identifier, WeakCodePlus)], [a])
polarizePlus xts = do
  let (xs, ts) = unzip xts
  (ys', yts') <- unzip <$> mapM polarize' ts
  return (ys', yts', xs)

polarizeMeta :: Meta -> WithEnv (WeakCodePlus, Maybe (Int, Int))
polarizeMeta m = do
  let (t, ml) = obtainInfoMeta m
  t' <- polarize t >>= reduceWeakCodePlus
  return (t', ml)

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
    (_, WeakCodeUpIntro pi@(_, WeakDataDown (_, WeakCodePi _ (_, WeakCodeUp int)))) -> do
      (x, varX) <- varOfType int
      (y, varY) <- varOfType int
      return
        ( negMeta (up pi ml) ml
        , WeakCodeUpIntro
            ( posMeta pi ml
            , WeakDataDownIntroPiIntro
                [(x, int), (y, int)]
                ( negMeta (up int ml) ml
                , WeakCodeTheta (ThetaArith op varX varY))))
    _ -> throwError "polarize.theta.arith"

polarizeThetaPrint :: Meta -> WithEnv WeakCodePlus
polarizeThetaPrint m = do
  (upT, ml) <- polarizeMeta m
  case upT of
    (_, WeakCodeUpIntro pi@(_, WeakDataDown (_, WeakCodePi [(_, int)] cod))) -> do
      (x, varX) <- varOfType int
      return
        ( negMeta (up pi ml) ml
        , WeakCodeUpIntro
            ( posMeta pi ml
            , WeakDataDownIntroPiIntro
                [(x, int)]
                (negMeta cod ml, WeakCodeTheta (ThetaPrint varX))))
    _ -> throwError "polarize.theta.print"

varOfType :: WeakDataPlus -> WithEnv (Identifier, WeakDataPlus)
varOfType t = do
  x <- newNameWith "arg"
  return (x, (posMeta t Nothing, WeakDataUpsilon x))
