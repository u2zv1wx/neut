{-# LANGUAGE OverloadedStrings #-}

module Reduce.Term
  ( reduceTermPlus
  , reduceIdentPlus
  , normalize
  ) where

import Control.Monad.State

import qualified Data.IntMap.Strict as IntMap

import Data.Basic
import Data.Env
import Data.Term

reduceTermPlus :: TermPlus -> TermPlus
reduceTermPlus (m, TermPi mName xts cod) = do
  let (ms, xs, ts) = unzip3 xts
  let ts' = map reduceTermPlus ts
  let cod' = reduceTermPlus cod
  (m, TermPi mName (zip3 ms xs ts') cod')
reduceTermPlus (m, TermPiIntro xts e) = do
  let (ms, xs, ts) = unzip3 xts
  let ts' = map reduceTermPlus ts
  let e' = reduceTermPlus e
  (m, TermPiIntro (zip3 ms xs ts') e')
reduceTermPlus (m, TermPiIntroNoReduce xts e) = do
  let (ms, xs, ts) = unzip3 xts
  let ts' = map reduceTermPlus ts
  let e' = reduceTermPlus e
  (m, TermPiIntroNoReduce (zip3 ms xs ts') e')
reduceTermPlus (m, TermPiIntroPlus ind (name, is, args1, args2) xts e) = do
  let args1' = map reduceIdentPlus args1
  let args2' = map reduceIdentPlus args2
  let xts' = map reduceIdentPlus xts
  let e' = reduceTermPlus e
  (m, TermPiIntroPlus ind (name, is, args1', args2') xts' e')
reduceTermPlus (m, TermPiElim e es) = do
  let e' = reduceTermPlus e
  let es' = map reduceTermPlus es
  let app = TermPiElim e' es'
  let valueCond = and $ map isValue es
  case e' of
    (_, TermPiIntro xts body) -- fixme: reduceできるだけreduceするようにする (partial evaluation)
      | length xts == length es'
      , valueCond -> do
        let xs = map (\(_, x, _) -> asInt x) xts
        reduceTermPlus $ substTermPlus (zip xs es') body
    (_, TermPiIntroPlus _ _ xts body)
      | length xts == length es'
      , valueCond -> do
        let xs = map (\(_, x, _) -> asInt x) xts
        reduceTermPlus $ substTermPlus (zip xs es') body
    _ -> (m, app)
reduceTermPlus (m, TermIter (mx, x, t) xts e)
  | x `notElem` varTermPlus e = reduceTermPlus (m, TermPiIntro xts e)
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
      | length es == length xts
      , k == k' -> do
        let xs = map (\(_, x, _) -> asInt x) xts
        reduceTermPlus $ substTermPlus (zip xs es) e2
    _ -> (m, TermArrayElim k xts e1' e2)
reduceTermPlus (m, TermStructIntro eks) = do
  let (es, ks) = unzip eks
  let es' = map reduceTermPlus es
  (m, TermStructIntro $ zip es' ks)
reduceTermPlus (m, TermStructElim xks e1 e2) = do
  let e1' = reduceTermPlus e1
  case e1' of
    (_, TermStructIntro eks)
      | (_, xs, ks1) <- unzip3 xks
      , (es, ks2) <- unzip eks
      , ks1 == ks2 -> reduceTermPlus $ substTermPlus (zip (map asInt xs) es) e2
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

reduceIdentPlus :: IdentifierPlus -> IdentifierPlus
reduceIdentPlus (m, x, t) = (m, x, reduceTermPlus t)

isValue :: TermPlus -> Bool
isValue (_, TermTau) = True
isValue (_, TermUpsilon _) = True
isValue (_, TermPi {}) = True
isValue (_, TermPiIntro {}) = True
isValue (_, TermPiIntroNoReduce {}) = True
isValue (_, TermPiIntroPlus {}) = True
isValue (_, TermIter {}) = True
isValue (_, TermConst x) = isValueConst x
-- isValue (_, TermFloat16 _) = True
-- isValue (_, TermFloat32 _) = True
-- isValue (_, TermFloat64 _) = True
isValue (_, TermFloat _ _) = True
isValue (_, TermEnum _) = True
isValue (_, TermEnumIntro _) = True
isValue (_, TermArray {}) = True
isValue (_, TermArrayIntro _ es) = and $ map isValue es
isValue (_, TermStruct {}) = True
isValue (_, TermStructIntro eks) = and $ map (isValue . fst) eks
isValue _ = False

isValueConst :: Identifier -> Bool
isValueConst (I (x, _))
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
normalize (m, TermPiIntro xts e) = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM normalize ts
  e' <- normalize e
  return (m, TermPiIntro (zip3 ms xs ts') e')
normalize (m, TermPiIntroNoReduce xts e) = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM normalize ts
  e' <- normalize e
  return (m, TermPiIntroNoReduce (zip3 ms xs ts') e')
normalize (m, TermPiIntroPlus ind (name, is, args1, args2) xts e) = do
  args1' <- mapM normalizeIdentPlus args1
  args2' <- mapM normalizeIdentPlus args2
  xts' <- mapM normalizeIdentPlus xts
  e' <- normalize e
  return (m, TermPiIntroPlus ind (name, is, args1', args2') xts' e')
normalize (m, TermPiElim e es) = do
  e' <- normalize e
  es' <- mapM normalize es
  case e' of
    (_, TermPiIntro xts body) -> do
      let xs = map (\(_, x, _) -> asInt x) xts
      normalize $ substTermPlus (zip xs es') body
    (_, TermPiIntroNoReduce xts body) -> do
      let xs = map (\(_, x, _) -> asInt x) xts
      normalize $ substTermPlus (zip xs es') body
    (_, TermPiIntroPlus _ _ xts body) -> do
      let xs = map (\(_, x, _) -> asInt x) xts
      normalize $ substTermPlus (zip xs es') body
    iter@(_, TermIter (_, self, _) xts body) -> do
      let xs = map (\(_, x, _) -> asInt x) xts
      normalize $ substTermPlus ((asInt self, iter) : zip xs es') body
    _ -> return (m, TermPiElim e' es')
normalize (m, TermIter (mx, x, t) xts e) = do
  t' <- normalize t
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM normalize ts
  e' <- normalize e
  return (m, TermIter (mx, x, t') (zip3 ms xs ts') e')
normalize (m, TermConst x) = do
  cenv <- gets cacheEnv
  case IntMap.lookup (asInt x) cenv of
    Just (Left e) -> normalize e
    _ -> return (m, TermConst x)
-- normalize (m, TermFloat16 x) = return (m, TermFloat16 x)
-- normalize (m, TermFloat32 x) = return (m, TermFloat32 x)
-- normalize (m, TermFloat64 x) = return (m, TermFloat64 x)
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
      | length es == length xts
      , k == k' -> do
        let xs = map (\(_, x, _) -> asInt x) xts
        normalize $ substTermPlus (zip xs es) e2
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
      | (_, xs, ks1) <- unzip3 xks
      , (es, ks2) <- unzip eks
      , ks1 == ks2 -> normalize $ substTermPlus (zip (map asInt xs) es) e2
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

normalizeIdentPlus :: IdentifierPlus -> WithEnv IdentifierPlus
normalizeIdentPlus (m, x, t) = do
  t' <- normalize t
  return (m, x, t')
