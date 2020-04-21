module Reduce.Term
  ( reduceTermPlus,
    reduceIdentPlus,
    normalize,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.Term
import qualified Data.Text as T

reduceTermPlus :: TermPlus -> TermPlus
reduceTermPlus (m, TermPi mName xts cod) = do
  let (ms, xs, ts) = unzip3 xts
  let ts' = map reduceTermPlus ts
  let cod' = reduceTermPlus cod
  (m, TermPi mName (zip3 ms xs ts') cod')
reduceTermPlus (m, TermPiIntro info xts e) = do
  let info' = fmap2 (map reduceIdentPlus) info
  let (ms, xs, ts) = unzip3 xts
  let ts' = map reduceTermPlus ts
  let e' = reduceTermPlus e
  (m, TermPiIntro info' (zip3 ms xs ts') e')
reduceTermPlus (m, TermPiElim e es) = do
  let e' = reduceTermPlus e
  let es' = map reduceTermPlus es
  let app = TermPiElim e' es'
  let valueCond = and $ map isValue es
  case e' of
    (_, TermPiIntro Nothing xts body) -- fixme: reduceできるだけreduceするようにする (partial evaluation)
      | length xts == length es',
        valueCond -> do
        let xs = map (\(_, x, _) -> asInt x) xts
        let sub = IntMap.fromList $ zip xs es'
        reduceTermPlus $ substTermPlus sub body
    _ -> (m, app)
reduceTermPlus (m, TermIter (mx, x, t) xts e)
  | x `notElem` varTermPlus e = reduceTermPlus (m, termPiIntro xts e)
  | otherwise = do
    let t' = reduceTermPlus t
    let (ms, xs, ts) = unzip3 xts
    let ts' = map reduceTermPlus ts
    let e' = reduceTermPlus e
    (m, TermIter (mx, x, t') (zip3 ms xs ts') e')
reduceTermPlus (m, TermEnumElim (e, t) les) = do
  let t' = reduceTermPlus t
  let e' = reduceTermPlus e
  let (ls, es) = unzip les
  let les'' = zip (map snd ls) es
  case e' of
    (_, TermEnumIntro l) ->
      case lookup (CaseValue l) les'' of
        Just body -> reduceTermPlus body
        Nothing ->
          case lookup CaseDefault les'' of
            Just body -> reduceTermPlus body
            Nothing -> do
              let es' = map reduceTermPlus es
              let les' = zip ls es'
              (m, TermEnumElim (e', t') les')
    _ -> do
      let es' = map reduceTermPlus es
      let les' = zip ls es'
      (m, TermEnumElim (e', t') les')
reduceTermPlus (m, TermArray dom k) = do
  let dom' = reduceTermPlus dom
  (m, TermArray dom' k)
reduceTermPlus (m, TermArrayIntro k es) = do
  let es' = map reduceTermPlus es
  (m, TermArrayIntro k es')
reduceTermPlus (m, TermArrayElim k xts e1 e2) = do
  let e1' = reduceTermPlus e1
  case e1 of
    (_, TermArrayIntro k' es)
      | length es == length xts,
        k == k' -> do
        let xs = map (\(_, x, _) -> asInt x) xts
        let sub = IntMap.fromList $ zip xs es
        reduceTermPlus $ substTermPlus sub e2
    _ -> (m, TermArrayElim k xts e1' e2)
reduceTermPlus (m, TermStructIntro eks) = do
  let (es, ks) = unzip eks
  let es' = map reduceTermPlus es
  (m, TermStructIntro $ zip es' ks)
reduceTermPlus (m, TermStructElim xks e1 e2) = do
  let e1' = reduceTermPlus e1
  case e1' of
    (_, TermStructIntro eks)
      | (_, xs, ks1) <- unzip3 xks,
        (es, ks2) <- unzip eks,
        ks1 == ks2 -> do
        let sub = IntMap.fromList $ zip (map asInt xs) es
        reduceTermPlus $ substTermPlus sub e2
    _ -> (m, TermStructElim xks e1' e2)
reduceTermPlus (m, TermCase indName e cxtes) = do
  let e' = reduceTermPlus e
  let cxtes'' =
        flip map cxtes $ \((c, xts), body) -> do
          let (ms, xs, ts) = unzip3 xts
          let ts' = map reduceTermPlus ts
          let body' = reduceTermPlus body
          ((c, zip3 ms xs ts'), body')
  (m, TermCase indName e' cxtes'')
reduceTermPlus t = t

reduceIdentPlus :: IdentPlus -> IdentPlus
reduceIdentPlus (m, x, t) = (m, x, reduceTermPlus t)

isValue :: TermPlus -> Bool
isValue (_, TermTau) = True
isValue (_, TermUpsilon _) = True
isValue (_, TermPi {}) = True
isValue (_, TermPiIntro {}) = True
isValue (_, TermIter {}) = True
isValue (_, TermConst x) = isValueConst x
isValue (_, TermFloat _ _) = True
isValue (_, TermEnum _) = True
isValue (_, TermEnumIntro _) = True
isValue (_, TermArray {}) = True
isValue (_, TermArrayIntro _ es) = and $ map isValue es
isValue (_, TermStruct {}) = True
isValue (_, TermStructIntro eks) = and $ map (isValue . fst) eks
isValue _ = False

isValueConst :: T.Text -> Bool
isValueConst x
  | Just _ <- asLowTypeMaybe x = True
  | Just _ <- asUnaryOpMaybe x = True
  | Just _ <- asBinaryOpMaybe x = True
  | x == "os:stdin" = True
  | x == "os:stdout" = True
  | x == "os:stderr" = True
  | otherwise = False

normalize :: TermPlus -> WithEnv TermPlus
normalize (m, TermTau) = return (m, TermTau)
normalize (m, TermUpsilon x) = return (m, TermUpsilon x)
normalize (m, TermPi mName xts cod) = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM normalize ts
  cod' <- normalize cod
  return (m, TermPi mName (zip3 ms xs ts') cod')
normalize (m, TermPiIntro info xts e) = do
  -- info' <- fmap2M (mapM normalizeIdentPlus) info
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM normalize ts
  e' <- normalize e
  -- return (m, TermPiIntro info' (zip3 ms xs ts') e')
  return (m, TermPiIntro info (zip3 ms xs ts') e')
normalize (m, TermPiElim e es) = do
  e' <- normalize e
  es' <- mapM normalize es
  case e' of
    (_, TermPiIntro _ xts body) -> do
      let xs = map (\(_, x, _) -> asInt x) xts
      let sub = IntMap.fromList $ zip xs es'
      normalize $ substTermPlus sub body
    iter@(_, TermIter (_, self, _) xts body) -> do
      let xs = map (\(_, x, _) -> asInt x) xts
      let sub = IntMap.fromList $ (asInt self, iter) : zip xs es'
      normalize $ substTermPlus sub body
    _ -> return (m, TermPiElim e' es')
normalize (m, TermIter (mx, x, t) xts e) = do
  t' <- normalize t
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM normalize ts
  e' <- normalize e
  return (m, TermIter (mx, x, t') (zip3 ms xs ts') e')
normalize (m, TermConst x) = do
  cenv <- gets cacheEnv
  case Map.lookup x cenv of
    Just (Left e) -> normalize e
    _ -> return (m, TermConst x)
normalize (m, TermBoxElim x) = return (m, TermBoxElim x)
normalize (m, TermFloat size x) = return (m, TermFloat size x)
normalize (m, TermEnum enumType) = return (m, TermEnum enumType)
normalize (m, TermEnumIntro enumValue) = return (m, TermEnumIntro enumValue)
normalize (m, TermEnumElim (e, t) les) = do
  t' <- normalize t
  e' <- normalize e
  let (ls, es) = unzip les
  let les'' = zip (map snd ls) es
  case e' of
    (_, TermEnumIntro l) ->
      case lookup (CaseValue l) les'' of
        Just body -> normalize body
        Nothing ->
          case lookup CaseDefault les'' of
            Just body -> normalize body
            Nothing -> do
              es' <- mapM normalize es
              let les' = zip ls es'
              return (m, TermEnumElim (e', t') les')
    _ -> do
      es' <- mapM normalize es
      let les' = zip ls es'
      return (m, TermEnumElim (e', t') les')
normalize (m, TermArray dom k) = do
  dom' <- normalize dom
  return (m, TermArray dom' k)
normalize (m, TermArrayIntro k es) = do
  es' <- mapM normalize es
  return (m, TermArrayIntro k es')
normalize (m, TermArrayElim k xts e1 e2) = do
  e1' <- normalize e1
  case e1 of
    (_, TermArrayIntro k' es)
      | length es == length xts,
        k == k' -> do
        let xs = map (\(_, x, _) -> asInt x) xts
        let sub = IntMap.fromList $ zip xs es
        normalize $ substTermPlus sub e2
    _ -> return (m, TermArrayElim k xts e1' e2)
normalize (m, TermStruct ks) = return (m, TermStruct ks)
normalize (m, TermStructIntro eks) = do
  let (es, ks) = unzip eks
  es' <- mapM normalize es
  return (m, TermStructIntro $ zip es' ks)
normalize (m, TermStructElim xks e1 e2) = do
  e1' <- normalize e1
  case e1' of
    (_, TermStructIntro eks)
      | (_, xs, ks1) <- unzip3 xks,
        (es, ks2) <- unzip eks,
        ks1 == ks2 -> do
        let sub = IntMap.fromList $ zip (map asInt xs) es
        normalize $ substTermPlus sub e2
    _ -> return (m, TermStructElim xks e1' e2)
normalize (m, TermCase indName e cxtes) = do
  e' <- normalize e
  cxtes'' <-
    flip mapM cxtes $ \((c, xts), body) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM normalize ts
      body' <- normalize body
      return ((c, zip3 ms xs ts'), body')
  return (m, TermCase indName e' cxtes'')

normalizeIdentPlus :: IdentPlus -> WithEnv IdentPlus
normalizeIdentPlus (m, x, t) = do
  t' <- normalize t
  return (m, x, t')
