module Reduce.WeakTerm
  ( reduceWeakTermPlus,
    substWeakTermPlus,
    substWeakTermPlus'',
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import qualified Data.Text as T
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
      let app = WeakTermPiElim e' es'
      case e' of
        (_, WeakTermPiIntro opacity LamKindNormal xts body)
          | not (isOpaque opacity),
            length xts == length es' -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            substWeakTermPlus' sub IntMap.empty (m, snd body) >>= reduceWeakTermPlus
        _ ->
          return (m, app)
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
              reduceWeakTermPlus (m, snd body)
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body ->
                  reduceWeakTermPlus (m, snd body)
                Nothing ->
                  return (m, WeakTermEnumElim (e', t') les')
        _ ->
          return (m, WeakTermEnumElim (e', t') les')
    (m, WeakTermQuestion e _) ->
      reduceWeakTermPlus (m, snd e)
    (m, WeakTermDerangement i t es) -> do
      es' <- mapM reduceWeakTermPlus es
      return (m, WeakTermDerangement i t es')
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
    (m, WeakTermVar opacity x)
      | Just x' <- IntMap.lookup (asInt x) nenv ->
        return (m, WeakTermVar opacity x')
      | Just e2 <- IntMap.lookup (asInt x) sub ->
        return e2
      | otherwise ->
        return term
    (m, WeakTermPi xts t) -> do
      (xts', t') <- substWeakTermPlus'' sub nenv xts t
      return (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix (mx, x, t) -> do
          t' <- substWeakTermPlus' sub nenv t
          x' <- newIdentFromIdent x
          let nenv' = IntMap.insert (asInt x) x' nenv
          (xts', e') <- substWeakTermPlus'' sub nenv' xts e
          return (m, WeakTermPiIntro opacity (LamKindFix (mx, x', t')) xts' e')
        _ -> do
          (xts', e') <- substWeakTermPlus'' sub nenv xts e
          return (m, WeakTermPiIntro opacity kind xts' e')
    (m, WeakTermPiElim e es) -> do
      e' <- substWeakTermPlus' sub nenv e
      es' <- mapM (substWeakTermPlus' sub nenv) es
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
    (m, WeakTermQuestion e t) -> do
      e' <- substWeakTermPlus' sub nenv e
      t' <- substWeakTermPlus' sub nenv t
      return (m, WeakTermQuestion e' t')
    (m, WeakTermDerangement i resultType es) -> do
      resultType' <- substWeakTermPlus' sub nenv resultType
      es' <- mapM (substWeakTermPlus' sub nenv) es
      return (m, WeakTermDerangement i resultType' es')
    (m, WeakTermCase resultType mSubject (e, t) clauseList) -> do
      resultType' <- substWeakTermPlus' sub nenv resultType
      mSubject' <- mapM (substWeakTermPlus' sub nenv) mSubject
      e' <- substWeakTermPlus' sub nenv e
      t' <- substWeakTermPlus' sub nenv t
      clauseList' <- forM clauseList $ \((name, xts), body) -> do
        (xts', body') <- substWeakTermPlus'' sub nenv xts body
        return ((name, xts'), body')
      return (m, WeakTermCase resultType' mSubject' (e', t') clauseList')

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
