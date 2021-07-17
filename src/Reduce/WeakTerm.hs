module Reduce.WeakTerm
  ( reduceWeakTermPlus,
    substWeakTermPlus,
  )
where

import Control.Monad
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import qualified Data.IntMap as IntMap
import qualified Data.Text as T
import Data.WeakTerm

reduceWeakTermPlus :: WeakTermPlus -> IO WeakTermPlus
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
            substWeakTermPlus sub body >>= reduceWeakTermPlus
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
        (_, WeakTermEnumIntro path l) ->
          case lookup (EnumCaseLabel path l) les'' of
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
      denv <- readIORef dataEnv
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
          clauseList' <- forM clauseList $ \((mPat, name, xts), body) -> do
            body' <- reduceWeakTermPlus body
            return ((mPat, name, xts), body')
          return (m, WeakTermCase resultType' mSubject' (e', t') clauseList')
    _ ->
      return term

checkClauseListSanity :: [T.Text] -> [(WeakPattern, WeakTermPlus)] -> Bool
checkClauseListSanity consNameList clauseList =
  case (consNameList, clauseList) of
    ([], []) ->
      True
    (consName : restConsNameList, ((_, name, _), _) : restClauseList)
      | consName == asText name ->
        checkClauseListSanity restConsNameList restClauseList
    _ ->
      False

toLamList :: Hint -> (WeakPattern, WeakTermPlus) -> WeakTermPlus
toLamList m ((_, _, xts), body) =
  (m, WeakTermPiIntro OpacityTransparent LamKindNormal xts body)

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> IO WeakTermPlus
substWeakTermPlus sub term =
  case term of
    (_, WeakTermTau) ->
      return term
    (_, WeakTermVar _ x)
      | Just e <- IntMap.lookup (asInt x) sub ->
        return e
      | otherwise ->
        return term
    (m, WeakTermPi xts t) -> do
      (xts', t') <- substWeakTermPlus' sub xts t
      return (m, WeakTermPi xts' t')
    (m, WeakTermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix xt -> do
          (xt' : xts', e') <- substWeakTermPlus' sub (xt : xts) e
          return (m, WeakTermPiIntro opacity (LamKindFix xt') xts' e')
        _ -> do
          (xts', e') <- substWeakTermPlus' sub xts e
          return (m, WeakTermPiIntro opacity kind xts' e')
    (m, WeakTermPiElim e es) -> do
      e' <- substWeakTermPlus sub e
      es' <- mapM (substWeakTermPlus sub) es
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
      t' <- substWeakTermPlus sub t
      return (m, WeakTermInt t' x)
    (m, WeakTermFloat t x) -> do
      t' <- substWeakTermPlus sub t
      return (m, WeakTermFloat t' x)
    (_, WeakTermEnum _ _) ->
      return term
    (_, WeakTermEnumIntro _ _) ->
      return term
    (m, WeakTermEnumElim (e, t) branchList) -> do
      t' <- substWeakTermPlus sub t
      e' <- substWeakTermPlus sub e
      let (caseList, es) = unzip branchList
      es' <- mapM (substWeakTermPlus sub) es
      return (m, WeakTermEnumElim (e', t') (zip caseList es'))
    (m, WeakTermQuestion e t) -> do
      e' <- substWeakTermPlus sub e
      t' <- substWeakTermPlus sub t
      return (m, WeakTermQuestion e' t')
    (m, WeakTermDerangement i es) -> do
      es' <- mapM (substWeakTermPlus sub) es
      return (m, WeakTermDerangement i es')
    (m, WeakTermCase resultType mSubject (e, t) clauseList) -> do
      resultType' <- substWeakTermPlus sub resultType
      mSubject' <- mapM (substWeakTermPlus sub) mSubject
      e' <- substWeakTermPlus sub e
      t' <- substWeakTermPlus sub t
      clauseList' <- forM clauseList $ \((mPat, name, xts), body) -> do
        (xts', body') <- substWeakTermPlus' sub xts body
        return ((mPat, name, xts'), body')
      return (m, WeakTermCase resultType' mSubject' (e', t') clauseList')
    (m, WeakTermIgnore e) -> do
      e' <- substWeakTermPlus sub e
      return (m, WeakTermIgnore e')

substWeakTermPlus' ::
  SubstWeakTerm ->
  [WeakIdentPlus] ->
  WeakTermPlus ->
  IO ([WeakIdentPlus], WeakTermPlus)
substWeakTermPlus' sub binder e =
  case binder of
    [] -> do
      e' <- substWeakTermPlus sub e
      return ([], e')
    ((m, x, t) : xts) -> do
      t' <- substWeakTermPlus sub t
      x' <- newIdentFromIdent x
      let sub' = IntMap.insert (asInt x) (m, WeakTermVar VarKindLocal x') sub
      (xts', e') <- substWeakTermPlus' sub' xts e
      return ((m, x', t') : xts', e')
