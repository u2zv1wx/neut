module Reduce.Term
  ( reduceTermPlus,
    normalize,
  )
where

import Control.Monad.State hiding (fix)
import Data.EnumCase
import Data.Env
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Primitive
import Data.Term
import qualified Data.Text as T

reduceTermPlus :: TermPlus -> TermPlus
reduceTermPlus term =
  case term of
    (m, TermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      let ts' = map reduceTermPlus ts
      let cod' = reduceTermPlus cod
      (m, TermPi (zip3 ms xs ts') cod')
    (m, TermPiIntro xts e) -> do
      let (ms, xs, ts) = unzip3 xts
      let ts' = map reduceTermPlus ts
      let e' = reduceTermPlus e
      (m, TermPiIntro (zip3 ms xs ts') e')
    (m, TermPiElim e es) -> do
      let e' = reduceTermPlus e
      let es' = map reduceTermPlus es
      let app = TermPiElim e' es'
      let valueCond = and $ map isValue es
      case e' of
        (_, TermPiIntro xts body) -- fixme: reduceできるだけreduceするようにする (partial evaluation)
          | length xts == length es',
            valueCond -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            reduceTermPlus $ substTermPlus sub body
        _ ->
          (m, app)
    (m, TermFix (mx, x, t) xts e)
      | x `notElem` varTermPlus e ->
        reduceTermPlus (m, TermPiIntro xts e)
      | otherwise -> do
        let t' = reduceTermPlus t
        let (ms, xs, ts) = unzip3 xts
        let ts' = map reduceTermPlus ts
        let e' = reduceTermPlus e
        (m, TermFix (mx, x, t') (zip3 ms xs ts') e')
    (m, TermEnumElim (e, t) les) -> do
      let t' = reduceTermPlus t
      let e' = reduceTermPlus e
      let (ls, es) = unzip les
      let les'' = zip (map snd ls) es
      case e' of
        (_, TermEnumIntro l) ->
          case lookup (EnumCaseLabel l) les'' of
            Just body ->
              reduceTermPlus body
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body ->
                  reduceTermPlus body
                Nothing -> do
                  let es' = map reduceTermPlus es
                  let les' = zip ls es'
                  (m, TermEnumElim (e', t') les')
        _ -> do
          let es' = map reduceTermPlus es
          let les' = zip ls es'
          (m, TermEnumElim (e', t') les')
    (m, TermArray dom k) -> do
      let dom' = reduceTermPlus dom
      (m, TermArray dom' k)
    (m, TermArrayIntro k es) -> do
      let es' = map reduceTermPlus es
      (m, TermArrayIntro k es')
    (m, TermArrayElim k xts e1 e2) -> do
      let e1' = reduceTermPlus e1
      case e1 of
        (_, TermArrayIntro k' es)
          | length es == length xts,
            k == k' -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es
            reduceTermPlus $ substTermPlus sub e2
        _ ->
          (m, TermArrayElim k xts e1' e2)
    (m, TermStructIntro eks) -> do
      let (es, ks) = unzip eks
      let es' = map reduceTermPlus es
      (m, TermStructIntro $ zip es' ks)
    (m, TermStructElim xks e1 e2) -> do
      let e1' = reduceTermPlus e1
      case e1' of
        (_, TermStructIntro eks)
          | (_, xs, ks1) <- unzip3 xks,
            (es, ks2) <- unzip eks,
            ks1 == ks2 -> do
            let sub = IntMap.fromList $ zip (map asInt xs) es
            reduceTermPlus $ substTermPlus sub e2
        _ ->
          (m, TermStructElim xks e1' e2)
    _ ->
      term

isValue :: TermPlus -> Bool
isValue term =
  case term of
    (_, TermTau) ->
      True
    (_, TermUpsilon _) ->
      True
    (_, TermPi {}) ->
      True
    (_, TermPiIntro {}) ->
      True
    (_, TermFix {}) ->
      True
    (_, TermConst x) ->
      isValueConst x
    (_, TermFloat _ _) ->
      True
    (_, TermEnum _) ->
      True
    (_, TermEnumIntro _) ->
      True
    (_, TermArray {}) ->
      True
    (_, TermArrayIntro _ es) ->
      and $ map isValue es
    (_, TermStruct {}) ->
      True
    (_, TermStructIntro eks) ->
      and $ map (isValue . fst) eks
    _ ->
      False

isValueConst :: T.Text -> Bool
isValueConst x
  | Just _ <- asLowTypeMaybe x =
    True
  | Just _ <- asUnaryOpMaybe x =
    True
  | Just _ <- asBinaryOpMaybe x =
    True
  | x == "os:stdin" =
    True
  | x == "os:stdout" =
    True
  | x == "os:stderr" =
    True
  | otherwise =
    False

normalize :: TermPlus -> WithEnv TermPlus
normalize term =
  case term of
    (m, TermTau) ->
      return (m, TermTau)
    (m, TermUpsilon x) -> do
      denv <- gets defEnv
      case IntMap.lookup (asInt x) denv of
        Just e ->
          normalize e
        Nothing ->
          return (m, TermUpsilon x)
    (m, TermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM normalize ts
      cod' <- normalize cod
      return (m, TermPi (zip3 ms xs ts') cod')
    (m, TermPiIntro xts e) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM normalize ts
      e' <- normalize e
      return (m, TermPiIntro (zip3 ms xs ts') e')
    (m, TermPiElim e es) -> do
      e' <- normalize e
      es' <- mapM normalize es
      case e' of
        (_, TermPiIntro xts body) -> do
          let xs = map (\(_, x, _) -> asInt x) xts
          let sub = IntMap.fromList $ zip xs es'
          normalize $ substTermPlus sub body
        fix@(_, TermFix (_, self, _) xts body) -> do
          let xs = map (\(_, x, _) -> asInt x) xts
          let sub = IntMap.fromList $ (asInt self, fix) : zip xs es'
          normalize $ substTermPlus sub body
        _ ->
          return (m, TermPiElim e' es')
    (m, TermFix (mx, x, t) xts e) -> do
      t' <- normalize t
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM normalize ts
      e' <- normalize e
      return (m, TermFix (mx, x, t') (zip3 ms xs ts') e')
    (m, TermConst x) ->
      return (m, TermConst x)
    (m, TermCall x) ->
      return (m, TermCall x)
    (m, TermInt size x) ->
      return (m, TermInt size x)
    (m, TermFloat size x) ->
      return (m, TermFloat size x)
    (m, TermEnum enumType) ->
      return (m, TermEnum enumType)
    (m, TermEnumIntro enumValue) ->
      return (m, TermEnumIntro enumValue)
    (m, TermEnumElim (e, t) les) -> do
      t' <- normalize t
      e' <- normalize e
      let (ls, es) = unzip les
      let les'' = zip (map snd ls) es
      case e' of
        (_, TermEnumIntro l) ->
          case lookup (EnumCaseLabel l) les'' of
            Just body ->
              normalize body
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body ->
                  normalize body
                Nothing -> do
                  es' <- mapM normalize es
                  let les' = zip ls es'
                  return (m, TermEnumElim (e', t') les')
        _ -> do
          es' <- mapM normalize es
          let les' = zip ls es'
          return (m, TermEnumElim (e', t') les')
    (m, TermArray dom k) -> do
      dom' <- normalize dom
      return (m, TermArray dom' k)
    (m, TermArrayIntro k es) -> do
      es' <- mapM normalize es
      return (m, TermArrayIntro k es')
    (m, TermArrayElim k xts e1 e2) -> do
      e1' <- normalize e1
      case e1 of
        (_, TermArrayIntro k' es)
          | length es == length xts,
            k == k' -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es
            normalize $ substTermPlus sub e2
        _ ->
          return (m, TermArrayElim k xts e1' e2)
    (m, TermStruct ks) ->
      return (m, TermStruct ks)
    (m, TermStructIntro eks) -> do
      let (es, ks) = unzip eks
      es' <- mapM normalize es
      return (m, TermStructIntro $ zip es' ks)
    (m, TermStructElim xks e1 e2) -> do
      e1' <- normalize e1
      case e1' of
        (_, TermStructIntro eks)
          | (_, xs, ks1) <- unzip3 xks,
            (es, ks2) <- unzip eks,
            ks1 == ks2 -> do
            let sub = IntMap.fromList $ zip (map asInt xs) es
            normalize $ substTermPlus sub e2
        _ ->
          return (m, TermStructElim xks e1' e2)
