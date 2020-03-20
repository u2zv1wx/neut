{-# LANGUAGE OverloadedStrings #-}

module Reduce.Term
  ( reduceTermPlus
  ) where

import Data.Basic
import Data.Env
import Data.Term

reduceTermPlus :: TermPlus -> WithEnv TermPlus
reduceTermPlus (m, TermPi mls xts cod) = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM reduceTermPlus ts
  cod' <- reduceTermPlus cod
  return $ (m, TermPi mls (zip3 ms xs ts') cod')
reduceTermPlus (m, TermPiPlus name mls xts cod) = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM reduceTermPlus ts
  cod' <- reduceTermPlus cod
  return $ (m, TermPiPlus name mls (zip3 ms xs ts') cod')
reduceTermPlus (m, TermPiIntro xts e) = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM reduceTermPlus ts
  e' <- reduceTermPlus e
  return $ (m, TermPiIntro (zip3 ms xs ts') e')
reduceTermPlus (m, TermPiIntroNoReduce xts e) = do
  let (ms, xs, ts) = unzip3 xts
  ts' <- mapM reduceTermPlus ts
  e' <- reduceTermPlus e
  return $ (m, TermPiIntroNoReduce (zip3 ms xs ts') e')
reduceTermPlus (m, TermPiIntroPlus ind (name, args) xts e) = do
  args' <- mapM reduceTermIdentPlus args
  xts' <- mapM reduceTermIdentPlus xts
  e' <- reduceTermPlus e
  return $ (m, TermPiIntroPlus ind (name, args') xts' e')
reduceTermPlus (m, TermPiElim e es) = do
  e' <- reduceTermPlus e
  es' <- mapM reduceTermPlus es
  let app = TermPiElim e' es'
  valueCond <- and <$> mapM isValue es
  case e' of
    (_, TermPiIntro xts body) -- fixme: reduceできるだけreduceするようにする (partial evaluation)
      | length xts == length es'
      , valueCond -> do
        let xs = map (\(_, x, _) -> x) xts
        reduceTermPlus $ substTermPlus (zip xs es') body
    (_, TermPiIntroPlus _ _ xts body)
      | length xts == length es'
      , valueCond -> do
        let xs = map (\(_, x, _) -> x) xts
        reduceTermPlus $ substTermPlus (zip xs es') body
    _ -> return (m, app)
reduceTermPlus (m, TermIter (mx, x, t) xts e)
  | x `notElem` varTermPlus e = reduceTermPlus (m, TermPiIntro xts e)
  | otherwise = do
    t' <- reduceTermPlus t
    let (ms, xs, ts) = unzip3 xts
    ts' <- mapM reduceTermPlus ts
    e' <- reduceTermPlus e
    return $ (m, TermIter (mx, x, t') (zip3 ms xs ts') e')
reduceTermPlus (m, TermConstDecl (mx, x, t) e) = do
  t' <- reduceTermPlus t
  e' <- reduceTermPlus e
  return (m, TermConstDecl (mx, x, t') e')
reduceTermPlus (m, TermEnumElim (e, t) les) = do
  t' <- reduceTermPlus t
  e' <- reduceTermPlus e
  let (ls, es) = unzip les
  case e' of
    (_, TermEnumIntro l) ->
      case lookup (CaseValue l) les of
        Just body -> reduceTermPlus body
        Nothing ->
          case lookup CaseDefault les of
            Just body -> reduceTermPlus body
            Nothing -> do
              es' <- mapM reduceTermPlus es
              let les' = zip ls es'
              return (m, TermEnumElim (e', t') les')
    _ -> do
      es' <- mapM reduceTermPlus es
      let les' = zip ls es'
      return (m, TermEnumElim (e', t') les')
reduceTermPlus (m, TermArray dom k) = do
  dom' <- reduceTermPlus dom
  return (m, TermArray dom' k)
reduceTermPlus (m, TermArrayIntro k es) = do
  es' <- mapM reduceTermPlus es
  return (m, TermArrayIntro k es')
reduceTermPlus (m, TermArrayElim k xts e1 e2) = do
  e1' <- reduceTermPlus e1
  case e1 of
    (_, TermArrayIntro k' es)
      | length es == length xts
      , k == k' -> do
        let xs = map (\(_, x, _) -> x) xts
        reduceTermPlus $ substTermPlus (zip xs es) e2
    _ -> return (m, TermArrayElim k xts e1' e2)
reduceTermPlus (m, TermStructIntro eks) = do
  let (es, ks) = unzip eks
  es' <- mapM reduceTermPlus es
  return (m, TermStructIntro $ zip es' ks)
reduceTermPlus (m, TermStructElim xks e1 e2) = do
  e1' <- reduceTermPlus e1
  case e1' of
    (_, TermStructIntro eks)
      | (_, xs, ks1) <- unzip3 xks
      , (es, ks2) <- unzip eks
      , ks1 == ks2 -> reduceTermPlus $ substTermPlus (zip xs es) e2
    _ -> return (m, TermStructElim xks e1' e2)
reduceTermPlus t = return t

reduceTermIdentPlus :: IdentifierPlus -> WithEnv IdentifierPlus
reduceTermIdentPlus (m, x, t) = do
  t' <- reduceTermPlus t
  return (m, x, t')

isValue :: TermPlus -> WithEnv Bool
isValue (_, TermTau _) = return True
isValue (_, TermUpsilon _) = return True
isValue (_, TermPi {}) = return True
isValue (_, TermPiPlus {}) = return True
isValue (_, TermPiIntro {}) = return True
isValue (_, TermPiIntroNoReduce {}) = return True
isValue (_, TermPiIntroPlus {}) = return True
isValue (_, TermSigma {}) = return True
isValue (_, TermSigmaIntro _ es) = do
  bs <- mapM isValue es
  return $ and bs
isValue (_, TermIter {}) = return True
isValue (_, TermConst x) = isValueConst x
isValue (_, TermFloat16 _) = return True
isValue (_, TermFloat32 _) = return True
isValue (_, TermFloat64 _) = return True
isValue (_, TermEnum _) = return True
isValue (_, TermEnumIntro _) = return True
isValue (_, TermArray {}) = return True
isValue (_, TermArrayIntro _ es) = do
  bs <- mapM isValue es
  return $ and bs
isValue (_, TermStruct {}) = return True
isValue (_, TermStructIntro eks) = do
  bs <- mapM (isValue . fst) eks
  return $ and bs
isValue _ = return False

isValueConst :: Identifier -> WithEnv Bool
isValueConst (I (x, _))
  | Just _ <- asLowTypeMaybe x = return True
  | Just _ <- asUnaryOpMaybe x = return True
  | Just _ <- asBinaryOpMaybe x = return True
  | otherwise = return False
