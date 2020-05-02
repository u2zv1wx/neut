module Reduce.WeakTerm
  ( reduceWeakTermPlus,
    reduceWeakTermWeakIdentPlus,
  )
where

import Data.EnumCase
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.Meta
import Data.WeakTerm

reduceWeakTermPlus :: WeakTermPlus -> WeakTermPlus
reduceWeakTermPlus term =
  case term of
    (m, WeakTermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      let ts' = map reduceWeakTermPlus ts
      let cod' = reduceWeakTermPlus cod
      (m, WeakTermPi (zip3 ms xs ts') cod')
    (_, WeakTermPiIntro xts (_, WeakTermPiElim e args))
      | Just ys <- mapM asUpsilon args,
        ys == map (\(_, x, _) -> x) xts ->
        e
    (m, WeakTermPiIntro xts e) -> do
      -- let info' = fmap (fmap (map reduceWeakTermWeakIdentPlus)) info
      let (ms, xs, ts) = unzip3 xts
      let ts' = map reduceWeakTermPlus ts
      let e' = reduceWeakTermPlus e
      (m, WeakTermPiIntro (zip3 ms xs ts') e')
    (m, WeakTermPiElim e es) -> do
      let e' = reduceWeakTermPlus e
      let es' = map reduceWeakTermPlus es
      let app = WeakTermPiElim e' es'
      case e' of
        (mLam, WeakTermPiIntro xts body)
          | length xts == length es',
            metaIsReducible mLam -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            reduceWeakTermPlus $ substWeakTermPlus sub body
        _ ->
          (m, app)
    (m, WeakTermFix (mx, x, t) xts e)
      | x `notElem` varWeakTermPlus e ->
        reduceWeakTermPlus (m, weakTermPiIntro xts e)
      | otherwise -> do
        let t' = reduceWeakTermPlus t
        let e' = reduceWeakTermPlus e
        let (ms, xs, ts) = unzip3 xts
        let ts' = map reduceWeakTermPlus ts
        (m, WeakTermFix (mx, x, t') (zip3 ms xs ts') e')
    (m, WeakTermEnumElim (e, t) les) -> do
      let e' = reduceWeakTermPlus e
      let (ls, es) = unzip les
      let es' = map reduceWeakTermPlus es
      let les' = zip ls es'
      let les'' = zip (map snd ls) es'
      let t' = reduceWeakTermPlus t
      case e' of
        (_, WeakTermEnumIntro l) ->
          case lookup (EnumCaseLabel l) les'' of
            Just body ->
              reduceWeakTermPlus body
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body -> reduceWeakTermPlus body
                Nothing -> (m, WeakTermEnumElim (e', t') les')
        _ ->
          (m, WeakTermEnumElim (e', t') les')
    (m, WeakTermArray dom k) -> do
      let dom' = reduceWeakTermPlus dom
      (m, WeakTermArray dom' k)
    (m, WeakTermArrayIntro k es) -> do
      let es' = map reduceWeakTermPlus es
      (m, WeakTermArrayIntro k es')
    (m, WeakTermArrayElim k xts e1 e2) -> do
      let e1' = reduceWeakTermPlus e1
      case e1' of
        (_, WeakTermArrayIntro k' es)
          | length es == length xts,
            k == k' -> do
            let (_, xs, _) = unzip3 xts
            let sub = IntMap.fromList $ zip (map asInt xs) es
            reduceWeakTermPlus $ substWeakTermPlus sub e2
        _ ->
          (m, WeakTermArrayElim k xts e1' e2)
    (m, WeakTermStructIntro eks) -> do
      let (es, ks) = unzip eks
      let es' = map reduceWeakTermPlus es
      (m, WeakTermStructIntro $ zip es' ks)
    (m, WeakTermStructElim xks e1 e2) -> do
      let e1' = reduceWeakTermPlus e1
      case e1' of
        (_, WeakTermStructIntro eks)
          | (_, xs, ks1) <- unzip3 xks,
            (es, ks2) <- unzip eks,
            ks1 == ks2 -> do
            let sub = IntMap.fromList $ zip (map asInt xs) es
            reduceWeakTermPlus $ substWeakTermPlus sub e2
        _ ->
          (m, WeakTermStructElim xks e1' e2)
    -- (m, WeakTermCase indName e cxtes) -> do
    --   let e' = reduceWeakTermPlus e
    --   let cxtes'' =
    --         flip map cxtes $ \((c, xts), body) -> do
    --           let (ms, xs, ts) = unzip3 xts
    --           let ts' = map reduceWeakTermPlus ts
    --           let body' = reduceWeakTermPlus body
    --           ((c, zip3 ms xs ts'), body')
    --   (m, WeakTermCase indName e' cxtes'')
    (_, WeakTermQuestion e _) ->
      reduceWeakTermPlus e
    _ -> term

reduceWeakTermWeakIdentPlus :: WeakIdentPlus -> WeakIdentPlus
reduceWeakTermWeakIdentPlus (m, x, t) =
  (m, x, reduceWeakTermPlus t)
