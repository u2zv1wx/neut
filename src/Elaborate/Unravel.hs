module Elaborate.Unravel
  ( unravel
  ) where

import Control.Monad.State

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.WeakTerm

unravel :: WeakTermPlus -> WithEnv WeakTermPlus
unravel (m, WeakTermTau l) = return (m, WeakTermTau l)
unravel (m, WeakTermUpsilon x) = do
  x' <- unravelUpsilon x
  return (m, WeakTermUpsilon x')
unravel (m, WeakTermPi mls xts t) = do
  (xts', t') <- unravelBinder xts t
  return (m, WeakTermPi mls xts' t')
unravel (m, WeakTermPiPlus name mls xts t) = do
  (xts', t') <- unravelBinder xts t
  return (m, WeakTermPiPlus name mls xts' t')
unravel (m, WeakTermPiIntro xts e) = do
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermPiIntro xts' e')
unravel (m, WeakTermPiIntroNoReduce xts e) = do
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermPiIntroNoReduce xts' e')
-- the "content" of this term is not used in toText, and so there's no need to unravel this term
unravel (m, WeakTermPiIntroPlus ind (name, args) xts e) =
  return (m, WeakTermPiIntroPlus ind (name, args) xts e)
unravel (m, WeakTermPiElim e es) = do
  e' <- unravel e
  es' <- mapM unravel es
  return (m, WeakTermPiElim e' es')
unravel (m, WeakTermSigma xts) =
  case splitLast xts of
    Nothing -> return (m, WeakTermSigma xts)
    Just (yts, (my, y, t)) -> do
      yts' <- unravelSigma yts
      t' <- unravel t
      return (m, WeakTermSigma $ yts' ++ [(my, y, t')])
unravel (m, WeakTermSigmaIntro t es) = do
  es' <- mapM unravel es
  -- don't rename t since it is not printed
  return (m, WeakTermSigmaIntro t es')
unravel (m, WeakTermSigmaElim t xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelBinder xts e2
  return (m, WeakTermSigmaElim t xts' e1' e2')
unravel (m, WeakTermIter (mx, x, t) xts e) = do
  x' <- unravelUpsilon x
  (xts', e') <- unravelBinder xts e
  return (m, WeakTermIter (mx, x', t) xts' e')
unravel (m, WeakTermConst x) = return (m, WeakTermConst x)
unravel (m, WeakTermZeta h) = do
  h' <- unravelZeta h
  return (m, WeakTermZeta h')
unravel (m, WeakTermInt t x) = do
  return (m, WeakTermInt t x)
unravel (m, WeakTermFloat16 x) = return (m, WeakTermFloat16 x)
unravel (m, WeakTermFloat32 x) = return (m, WeakTermFloat32 x)
unravel (m, WeakTermFloat64 x) = return (m, WeakTermFloat64 x)
unravel (m, WeakTermFloat t x) = do
  return (m, WeakTermFloat t x)
unravel (m, WeakTermEnum s) = return (m, WeakTermEnum s)
unravel (m, WeakTermEnumIntro x) = return (m, WeakTermEnumIntro x)
unravel (m, WeakTermEnumElim (e, t) caseList) = do
  e' <- unravel e
  caseList' <- unravelCaseList caseList
  return (m, WeakTermEnumElim (e', t) caseList')
unravel (m, WeakTermArray dom kind) = do
  dom' <- unravel dom
  return (m, WeakTermArray dom' kind)
unravel (m, WeakTermArrayIntro kind es) = do
  es' <- mapM unravel es
  return (m, WeakTermArrayIntro kind es')
unravel (m, WeakTermArrayElim kind xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelBinder xts e2
  return (m, WeakTermArrayElim kind xts' e1' e2')
unravel (m, WeakTermStruct ts) = return (m, WeakTermStruct ts)
unravel (m, WeakTermStructIntro ets) = do
  let (es, ts) = unzip ets
  es' <- mapM unravel es
  return (m, WeakTermStructIntro $ zip es' ts)
unravel (m, WeakTermStructElim xts e1 e2) = do
  e1' <- unravel e1
  (xts', e2') <- unravelStruct xts e2
  return (m, WeakTermStructElim xts' e1' e2')
unravel (m, WeakTermCase (e, t) cxtes) = do
  e' <- unravel e
  t' <- unravel t
  cxtes' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      (xts', body') <- unravelBinder xts body
      return ((c, xts'), body')
  return (m, WeakTermCase (e', t') cxtes')

unravelUpsilon :: Identifier -> WithEnv Identifier
unravelUpsilon (I (s, i)) = do
  nenv <- gets nameEnv
  case Map.lookup s nenv of
    Just s' -> return $ I (s', i)
    Nothing -> do
      j <- newCount
      let s' = T.pack $ "var" ++ show j
      modify (\e -> e {nameEnv = Map.insert s s' nenv})
      return $ I (s', i)

unravelZeta :: Identifier -> WithEnv Identifier
unravelZeta (I (s, i)) = do
  rnenv <- gets revNameEnv
  case IntMap.lookup i rnenv of
    Just j -> return $ I (s, j)
    Nothing -> do
      j <- newCount
      modify (\env -> env {revNameEnv = IntMap.insert i j rnenv})
      return $ I (s, j)

unravelBinder ::
     [IdentifierPlus]
  -> WeakTermPlus
  -> WithEnv ([IdentifierPlus], WeakTermPlus)
unravelBinder [] e = do
  e' <- unravel e
  return ([], e')
unravelBinder ((mx, x, t):xts) e = do
  t' <- unravel t
  x' <- unravelUpsilon x
  (xts', e') <- unravelBinder xts e
  return ((mx, x', t') : xts', e')

unravelSigma :: [IdentifierPlus] -> WithEnv [IdentifierPlus]
unravelSigma [] = return []
unravelSigma ((mx, x, t):xts) = do
  t' <- unravel t
  x' <- unravelUpsilon x
  xts' <- unravelSigma xts
  return $ (mx, x', t') : xts'

unravelCaseList ::
     [(WeakCase, WeakTermPlus)] -> WithEnv [(WeakCase, WeakTermPlus)]
unravelCaseList caseList = do
  let (ls, es) = unzip caseList
  ls' <- mapM unravelWeakCase ls
  es' <- mapM unravel es
  return $ zip ls' es'

unravelWeakCase :: WeakCase -> WithEnv WeakCase
unravelWeakCase (WeakCaseInt t a) = do
  t' <- unravel t
  return $ WeakCaseInt t' a
unravelWeakCase l = return l

unravelStruct ::
     [(Meta, Identifier, ArrayKind)]
  -> WeakTermPlus
  -> WithEnv ([(Meta, Identifier, ArrayKind)], WeakTermPlus)
unravelStruct [] e = do
  e' <- unravel e
  return ([], e')
unravelStruct ((mx, x, t):xts) e = do
  x' <- unravelUpsilon x
  (xts', e') <- unravelStruct xts e
  return ((mx, x', t) : xts', e')
