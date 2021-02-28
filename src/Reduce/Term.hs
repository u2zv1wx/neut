module Reduce.Term
  ( reduceTermPlus,
  )
where

import Data.EnumCase
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Namespace
import Data.Primitive
import qualified Data.Set as S
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
        (_, TermPiIntro xts body)
          | length xts == length es',
            valueCond -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            reduceTermPlus $ substTermPlus sub body
        _ ->
          (m, app)
    (m, TermFix (mx, x, t) xts e) -> do
      let lam@(_, TermPiIntro xts' e') = reduceTermPlus (m, TermPiIntro xts e)
      if asInt x `S.notMember` varTermPlus e'
        then lam
        else (m, TermFix (mx, x, reduceTermPlus t) xts' e')
    (m, TermEnumElim (e, t) les) -> do
      let t' = reduceTermPlus t
      let e' = reduceTermPlus e
      let (ls, es) = unzip les
      let les'' = zip (map snd ls) es
      case e' of
        (_, TermEnumIntro l)
          | Just body <- lookup (EnumCaseLabel l) les'' ->
            reduceTermPlus body
          | Just body <- lookup EnumCaseDefault les'' ->
            reduceTermPlus body
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
    (m, TermExploit i t ekts) -> do
      let (es, ks, ts) = unzip3 ekts
      let es' = map reduceTermPlus es
      let ts' = map reduceTermPlus ts
      (m, TermExploit i t (zip3 es' ks ts'))
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
    (_, TermInt _ _) ->
      True
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
  | x == "os" <> nsSep <> "stdin" =
    True
  | x == "os" <> nsSep <> "stdout" =
    True
  | x == "os" <> nsSep <> "stderr" =
    True
  | otherwise =
    False
