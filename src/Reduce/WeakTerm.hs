module Reduce.WeakTerm
  ( reduceWeakTermPlus,
    subWT,
    -- substWeakTermPlus,
    -- substWeakTermPlus'',
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import qualified Data.Text as T
import Data.WeakTerm

reduceWeakTermPlus :: WeakTermPlus -> WithEnv WeakTermPlus
reduceWeakTermPlus term =
  case term of
    (m, WeakTermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM reduceWeakTermPlus ts
      cod' <- reduceWeakTermPlus cod
      return (m, WeakTermPi (zip3 ms xs ts') cod')
    (m, WeakTermPiIntro opacity kind xts e)
      | LamKindFix (_, x, _) <- kind,
        x `notElem` varWeakTermPlus e ->
        reduceWeakTermPlus (m, WeakTermPiIntro opacity LamKindNormal xts e)
      | otherwise -> do
        let (ms, xs, ts) = unzip3 xts
        ts' <- mapM reduceWeakTermPlus ts
        e' <- reduceWeakTermPlus e
        case kind of
          LamKindFix (mx, x, t) -> do
            t' <- reduceWeakTermPlus t
            return (m, WeakTermPiIntro opacity (LamKindFix (mx, x, t')) (zip3 ms xs ts') e')
          _ ->
            return (m, WeakTermPiIntro opacity kind (zip3 ms xs ts') e')
    (m, WeakTermPiElim e es) -> do
      e' <- reduceWeakTermPlus e
      es' <- mapM reduceWeakTermPlus es
      case e' of
        (_, WeakTermPiIntro opacity LamKindNormal xts body)
          | not (isOpaque opacity),
            length xts == length es' -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            -- reduceWeakTermPlus $ substWeakTermPlus sub (m, snd body)
            -- subWT sub (m, snd body) >>= reduceWeakTermPlus
            subWT sub body >>= reduceWeakTermPlus
        -- substWeakTermPlus' sub IntMap.empty (m, snd body) >>= reduceWeakTermPlus
        _ ->
          return (m, WeakTermPiElim e' es')
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
    (_, WeakTermQuestion e _) ->
      reduceWeakTermPlus e
    (m, WeakTermDerangement i es) -> do
      es' <- mapM reduceWeakTermPlus es
      return (m, WeakTermDerangement i es')
    (m, WeakTermCase resultType mSubject (e, t) clauseList) -> do
      e' <- reduceWeakTermPlus e
      let lamList = map (toLamList m) clauseList
      denv <- gets dataEnv
      case e' of
        (_, WeakTermPiIntro opacity (LamKindCons dataName consName) _ _)
          | not (isOpaque opacity),
            Just consNameList <- Map.lookup dataName denv,
            consName `elem` consNameList,
            checkClauseListSanity consNameList clauseList -> do
            let app = (m, WeakTermPiElim e' (resultType : lamList))
            reduceWeakTermPlus app
        _ -> do
          resultType' <- reduceWeakTermPlus resultType
          mSubject' <- mapM reduceWeakTermPlus mSubject
          t' <- reduceWeakTermPlus t
          clauseList' <- forM clauseList $ \((name, xts), body) -> do
            body' <- reduceWeakTermPlus body
            return ((name, xts), body')
          return (m, WeakTermCase resultType' mSubject' (e', t') clauseList')
    _ ->
      return term

checkClauseListSanity :: [T.Text] -> [(WeakPattern, WeakTermPlus)] -> Bool
checkClauseListSanity consNameList clauseList =
  case (consNameList, clauseList) of
    ([], []) ->
      True
    (consName : restConsNameList, ((name, _), _) : restClauseList)
      | consName == asText name ->
        checkClauseListSanity restConsNameList restClauseList
    _ ->
      False

toLamList :: Hint -> (WeakPattern, WeakTermPlus) -> WeakTermPlus
toLamList m ((_, xts), body) =
  (m, WeakTermPiIntro OpacityTransparent LamKindNormal xts body)

subWT ::
  SubstWeakTerm ->
  WeakTermPlus ->
  WithEnv WeakTermPlus
subWT sub term =
  case term of
    (_, WeakTermTau) ->
      return term
    (_, WeakTermVar _ x)
      | Just e <- IntMap.lookup (asInt x) sub ->
        return e
      | otherwise ->
        return term
    (m, WeakTermPi xts t) -> do
      (xts', t') <- subWT' sub xts t
      return (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix xt -> do
          (xt' : xts', e') <- subWT' sub (xt : xts) e
          return (m, WeakTermPiIntro opacity (LamKindFix xt') xts' e')
        _ -> do
          (xts', e') <- subWT' sub xts e
          return (m, WeakTermPiIntro opacity kind xts' e')
    (m, WeakTermPiElim e es) -> do
      e' <- subWT sub e
      es' <- mapM (subWT sub) es
      return (m, WeakTermPiElim e' es')
    (_, WeakTermConst _) ->
      return term
    (_, WeakTermAster x) ->
      case IntMap.lookup x sub of
        Nothing ->
          return term
        Just e2 ->
          return e2
    (m, WeakTermInt t x) -> do
      t' <- subWT sub t
      return (m, WeakTermInt t' x)
    (m, WeakTermFloat t x) -> do
      t' <- subWT sub t
      return (m, WeakTermFloat t' x)
    (m, WeakTermEnum x) ->
      return (m, WeakTermEnum x)
    (m, WeakTermEnumIntro l) ->
      return (m, WeakTermEnumIntro l)
    (m, WeakTermEnumElim (e, t) branchList) -> do
      t' <- subWT sub t
      e' <- subWT sub e
      let (caseList, es) = unzip branchList
      es' <- mapM (subWT sub) es
      return (m, WeakTermEnumElim (e', t') (zip caseList es'))
    (m, WeakTermQuestion e t) -> do
      e' <- subWT sub e
      t' <- subWT sub t
      return (m, WeakTermQuestion e' t')
    (m, WeakTermDerangement i es) -> do
      es' <- mapM (subWT sub) es
      return (m, WeakTermDerangement i es')
    (m, WeakTermCase resultType mSubject (e, t) clauseList) -> do
      resultType' <- subWT sub resultType
      mSubject' <- mapM (subWT sub) mSubject
      e' <- subWT sub e
      t' <- subWT sub t
      clauseList' <- forM clauseList $ \((name, xts), body) -> do
        (xts', body') <- subWT' sub xts body
        return ((name, xts'), body')
      return (m, WeakTermCase resultType' mSubject' (e', t') clauseList')

subWT' ::
  SubstWeakTerm ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  WithEnv ([WeakIdentPlus], WeakTermPlus)
subWT' sub binder e =
  case binder of
    [] -> do
      e' <- subWT sub e
      return ([], e')
    ((m, x, t) : xts) -> do
      t' <- subWT sub t
      x' <- newIdentFromIdent x
      let sub' = IntMap.insert (asInt x) (m, WeakTermVar VarKindLocal x') sub
      (xts', e') <- subWT' sub' xts e
      return ((m, x', t') : xts', e')

-- t' <- subWT sub nenv t
-- x' <- newIdentFromIdent x
-- let nenv' = IntMap.insert (asInt x) x' nenv
-- (xts', e') <- subWT' sub nenv' xts e
-- return ((m, x', t') : xts', e')

-- substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WeakTermPlus
-- substWeakTermPlus sub term =
--   substWeakTermPlus' sub S.empty term

-- substWeakTermPlus' :: SubstWeakTerm -> NameSet -> WeakTermPlus -> WeakTermPlus
-- substWeakTermPlus' sub nenv term =
--   case term of
--     (_, WeakTermTau) ->
--       term
--     (_, WeakTermVar _ x)
--       | S.notMember (asInt x) nenv,
--         Just e2 <- IntMap.lookup (asInt x) sub -> do
--         let fvs = varWeakTermPlus e2
--         if any (\y -> S.member (asInt y) nenv) fvs
--           then undefined
--           else e2
--       | otherwise ->
--         term
--     (m, WeakTermPi xts t) -> do
--       let (xts', t') = substWeakTermPlus'' sub nenv xts t
--       (m, WeakTermPi xts' t')
--     (m, WeakTermPiIntro opacity kind xts e) -> do
--       case kind of
--         LamKindFix xt -> do
--           let (xt' : xts', e') = substWeakTermPlus'' sub nenv (xt : xts) e
--           (m, WeakTermPiIntro opacity (LamKindFix xt') xts' e')
--         _ -> do
--           let (xts', e') = substWeakTermPlus'' sub nenv xts e
--           (m, WeakTermPiIntro opacity kind xts' e')
--     (m, WeakTermPiElim e es) -> do
--       let e' = substWeakTermPlus' sub nenv e
--       let es' = map (substWeakTermPlus' sub nenv) es
--       (m, WeakTermPiElim e' es')
--     (_, WeakTermConst _) ->
--       term
--     (_, WeakTermAster x) ->
--       case IntMap.lookup x sub of
--         Nothing ->
--           term
--         Just e2 ->
--           e2
--     (m, WeakTermInt t x) -> do
--       let t' = substWeakTermPlus' sub nenv t
--       (m, WeakTermInt t' x)
--     (m, WeakTermFloat t x) -> do
--       let t' = substWeakTermPlus' sub nenv t
--       (m, WeakTermFloat t' x)
--     (m, WeakTermEnum x) ->
--       (m, WeakTermEnum x)
--     (m, WeakTermEnumIntro l) ->
--       (m, WeakTermEnumIntro l)
--     (m, WeakTermEnumElim (e, t) branchList) -> do
--       let t' = substWeakTermPlus' sub nenv t
--       let e' = substWeakTermPlus' sub nenv e
--       let (caseList, es) = unzip branchList
--       let es' = map (substWeakTermPlus' sub nenv) es
--       (m, WeakTermEnumElim (e', t') (zip caseList es'))
--     (m, WeakTermQuestion e t) -> do
--       let e' = substWeakTermPlus' sub nenv e
--       let t' = substWeakTermPlus' sub nenv t
--       (m, WeakTermQuestion e' t')
--     (m, WeakTermDerangement i es) -> do
--       let es' = map (substWeakTermPlus' sub nenv) es
--       (m, WeakTermDerangement i es')
--     (m, WeakTermCase resultType mSubject (e, t) clauseList) -> do
--       let resultType' = substWeakTermPlus' sub nenv resultType
--       let mSubject' = fmap (substWeakTermPlus' sub nenv) mSubject
--       let e' = substWeakTermPlus' sub nenv e
--       let t' = substWeakTermPlus' sub nenv t
--       let clauseList' = flip map clauseList $ \((name, xts), body) -> do
--             let (xts', body') = substWeakTermPlus'' sub nenv xts body
--             ((name, xts'), body')
--       (m, WeakTermCase resultType' mSubject' (e', t') clauseList')

-- substWeakTermPlus'' ::
--   SubstWeakTerm ->
--   NameSet ->
--   [WeakIdentPlus] ->
--   WeakTermPlus ->
--   ([WeakIdentPlus], WeakTermPlus)
-- substWeakTermPlus'' sub nenv binder e =
--   case binder of
--     [] -> do
--       let e' = substWeakTermPlus' sub nenv e
--       ([], e')
--     ((m, x, t) : xts) -> do
--       let t' = substWeakTermPlus' sub nenv t
--       let sub' = IntMap.delete (asInt x) sub
--       let (xts', e') = substWeakTermPlus'' sub' (S.insert (asInt x) nenv) xts e
--       ((m, x, t') : xts', e')
