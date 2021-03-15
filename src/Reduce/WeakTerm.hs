module Reduce.WeakTerm
  ( reduceWeakTermPlus,
    substWeakTermPlus,
    substWeakTermPlus'',
  )
where

import Data.Basic
import Data.Env
import qualified Data.IntMap as IntMap
import Data.WeakTerm

type NameEnv = IntMap.IntMap Ident

reduceWeakTermPlus :: WeakTermPlus -> WithEnv WeakTermPlus
reduceWeakTermPlus term =
  case term of
    (m, WeakTermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM reduceWeakTermPlus ts
      cod' <- reduceWeakTermPlus cod
      return (m, WeakTermPi (zip3 ms xs ts') cod')
    (m, WeakTermPiIntro xts e) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM reduceWeakTermPlus ts
      e' <- reduceWeakTermPlus e
      return (m, WeakTermPiIntro (zip3 ms xs ts') e')
    (m, WeakTermPiElim e es) -> do
      e' <- reduceWeakTermPlus e
      es' <- mapM reduceWeakTermPlus es
      let app = WeakTermPiElim e' es'
      case e' of
        (_, WeakTermPiIntro xts body)
          | length xts == length es' -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            substWeakTermPlus' sub IntMap.empty body >>= reduceWeakTermPlus
        _ ->
          return (m, app)
    (m, WeakTermFix (mx, x, t) xts e)
      | x `notElem` varWeakTermPlus e ->
        reduceWeakTermPlus (m, WeakTermPiIntro xts e)
      | otherwise -> do
        t' <- reduceWeakTermPlus t
        e' <- reduceWeakTermPlus e
        let (ms, xs, ts) = unzip3 xts
        ts' <- mapM reduceWeakTermPlus ts
        return (m, WeakTermFix (mx, x, t') (zip3 ms xs ts') e')
    (m, WeakTermEnumElim (e, t) les) -> do
      e' <- reduceWeakTermPlus e
      let (ls, es) = unzip les
      es' <- mapM reduceWeakTermPlus es
      let les' = zip ls es'
      let les'' = zip (map snd ls) es'
      t' <- reduceWeakTermPlus t
      case e' of
        (_, WeakTermEnumIntro l) ->
          case lookup (EnumCaseLabel l) les'' of
            Just body ->
              reduceWeakTermPlus body
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body ->
                  reduceWeakTermPlus body
                Nothing ->
                  return (m, WeakTermEnumElim (e', t') les')
        _ ->
          return (m, WeakTermEnumElim (e', t') les')
    (m, WeakTermTensor ts) -> do
      ts' <- mapM reduceWeakTermPlus ts
      return (m, WeakTermTensor ts')
    (m, WeakTermTensorIntro es) -> do
      es' <- mapM reduceWeakTermPlus es
      return (m, WeakTermTensorIntro es')
    (m, WeakTermTensorElim xts e1 e2) -> do
      e1' <- reduceWeakTermPlus e1
      case e1' of
        (_, WeakTermTensorIntro es)
          | length es == length xts -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es
            substWeakTermPlus' sub IntMap.empty e2 >>= reduceWeakTermPlus
        _ -> do
          e2' <- reduceWeakTermPlus e2
          let (ms, xs, ts) = unzip3 xts
          ts' <- mapM reduceWeakTermPlus ts
          return (m, WeakTermTensorElim (zip3 ms xs ts') e1' e2')
    (_, WeakTermQuestion e _) ->
      reduceWeakTermPlus e
    (m, WeakTermDerangement i t ekts) -> do
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM reduceWeakTermPlus es
      ts' <- mapM reduceWeakTermPlus ts
      return (m, WeakTermDerangement i t (zip3 es' ks ts'))
    _ ->
      return term

substWeakTermPlus ::
  SubstWeakTerm ->
  WeakTermPlus ->
  WithEnv WeakTermPlus
substWeakTermPlus sub term =
  if IntMap.null sub
    then return term
    else substWeakTermPlus' sub IntMap.empty term

substWeakTermPlus' ::
  SubstWeakTerm ->
  NameEnv ->
  WeakTermPlus ->
  WithEnv WeakTermPlus
substWeakTermPlus' sub nenv term =
  case term of
    (_, WeakTermTau) ->
      return term
    (m, WeakTermUpsilon x)
      | Just x' <- IntMap.lookup (asInt x) nenv ->
        return (m, WeakTermUpsilon x')
      | Just e2@(_, e) <- IntMap.lookup (asInt x) sub ->
        return (supHint (metaOf term) (metaOf e2), e)
      | otherwise ->
        return term
    (m, WeakTermPi xts t) -> do
      (xts', t') <- substWeakTermPlus'' sub nenv xts t
      return (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro xts body) -> do
      (xts', body') <- substWeakTermPlus'' sub nenv xts body
      return (m, WeakTermPiIntro xts' body')
    (m, WeakTermPiElim e es) -> do
      e' <- substWeakTermPlus' sub nenv e
      es' <- mapM (substWeakTermPlus' sub nenv) es
      return (m, WeakTermPiElim e' es')
    (m, WeakTermFix (mx, x, t) xts e) -> do
      t' <- substWeakTermPlus' sub nenv t
      x' <- newIdentFromIdent x
      let nenv' = IntMap.insert (asInt x) x' nenv
      (xts', e') <- substWeakTermPlus'' sub nenv' xts e
      return (m, WeakTermFix (mx, x', t') xts' e')
    (_, WeakTermConst _) ->
      return term
    (_, WeakTermAster x) ->
      case IntMap.lookup x sub of
        Nothing ->
          return term
        Just e2@(_, e) ->
          return (supHint (metaOf term) (metaOf e2), e)
    (m, WeakTermInt t x) -> do
      t' <- substWeakTermPlus' sub nenv t
      return (m, WeakTermInt t' x)
    (m, WeakTermFloat t x) -> do
      t' <- substWeakTermPlus' sub nenv t
      return (m, WeakTermFloat t' x)
    (m, WeakTermEnum x) ->
      return (m, WeakTermEnum x)
    (m, WeakTermEnumIntro l) ->
      return (m, WeakTermEnumIntro l)
    (m, WeakTermEnumElim (e, t) branchList) -> do
      t' <- substWeakTermPlus' sub nenv t
      e' <- substWeakTermPlus' sub nenv e
      let (caseList, es) = unzip branchList
      es' <- mapM (substWeakTermPlus' sub nenv) es
      return (m, WeakTermEnumElim (e', t') (zip caseList es'))
    (m, WeakTermTensor ts) -> do
      ts' <- mapM (substWeakTermPlus' sub nenv) ts
      return (m, WeakTermTensor ts')
    (m, WeakTermTensorIntro es) -> do
      es' <- mapM (substWeakTermPlus' sub nenv) es
      return (m, WeakTermTensorIntro es')
    (m, WeakTermTensorElim xts e1 e2) -> do
      e1' <- substWeakTermPlus' sub nenv e1
      (xts', e2') <- substWeakTermPlus'' sub nenv xts e2
      return (m, WeakTermTensorElim xts' e1' e2')
    (m, WeakTermQuestion e t) -> do
      e' <- substWeakTermPlus' sub nenv e
      t' <- substWeakTermPlus' sub nenv t
      return (m, WeakTermQuestion e' t')
    (m, WeakTermDerangement i resultType ekts) -> do
      resultType' <- substWeakTermPlus' sub nenv resultType
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM (substWeakTermPlus' sub nenv) es
      ts' <- mapM (substWeakTermPlus' sub nenv) ts
      return (m, WeakTermDerangement i resultType' (zip3 es' ks ts'))

substWeakTermPlus'' ::
  SubstWeakTerm ->
  NameEnv ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], WeakTermPlus)
substWeakTermPlus'' sub nenv binder e =
  case binder of
    [] -> do
      e' <- substWeakTermPlus' sub nenv e
      return ([], e')
    ((m, x, t) : xts) -> do
      x' <- newIdentFromIdent x
      let nenv' = IntMap.insert (asInt x) x' nenv
      (xts', e') <- substWeakTermPlus'' sub nenv' xts e
      t' <- substWeakTermPlus' sub nenv t
      return ((m, x', t') : xts', e')
