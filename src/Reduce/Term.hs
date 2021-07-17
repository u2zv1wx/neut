module Reduce.Term
  ( reduceTermPlus,
  )
where

import Control.Monad
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import qualified Data.IntMap as IntMap
import Data.Term
import qualified Data.Text as T

-- reduce given term assuming its purity
reduceTermPlus :: TermPlus -> IO TermPlus
reduceTermPlus term =
  case term of
    (m, TermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM reduceTermPlus ts
      cod' <- reduceTermPlus cod
      return (m, TermPi (zip3 ms xs ts') cod')
    (m, TermPiIntro opacity kind xts e) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM reduceTermPlus ts
      e' <- reduceTermPlus e
      case kind of
        LamKindFix (mx, x, t) -> do
          t' <- reduceTermPlus t
          return (m, TermPiIntro opacity (LamKindFix (mx, x, t')) (zip3 ms xs ts') e')
        _ ->
          return (m, TermPiIntro opacity kind (zip3 ms xs ts') e')
    (m, TermPiElim e es) -> do
      e' <- reduceTermPlus e
      es' <- mapM reduceTermPlus es
      let app = TermPiElim e' es'
      case e' of
        (_, TermPiIntro opacity LamKindNormal xts body)
          | not (isOpaque opacity),
            length xts == length es' -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            substTermPlus sub (m, snd body) >>= reduceTermPlus
        _ ->
          return (m, app)
    (m, TermEnumElim (e, t) les) -> do
      e' <- reduceTermPlus e
      let (ls, es) = unzip les
      es' <- mapM reduceTermPlus es
      let les' = zip ls es'
      let les'' = zip (map snd ls) es'
      t' <- reduceTermPlus t
      case e' of
        (_, TermEnumIntro fp l) ->
          case lookup (EnumCaseLabel fp l) les'' of
            Just body ->
              reduceTermPlus (m, snd body)
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body ->
                  reduceTermPlus (m, snd body)
                Nothing ->
                  return (m, TermEnumElim (e', t') les')
        _ ->
          return (m, TermEnumElim (e', t') les')
    (m, TermDerangement i es) -> do
      es' <- mapM reduceTermPlus es
      return (m, TermDerangement i es')
    (m, TermCase resultType mSubject (e, t) clauseList) -> do
      e' <- reduceTermPlus e
      let lamList = map (toLamList m) clauseList
      denv <- readIORef dataEnv
      case e' of
        (_, TermPiIntro opacity (LamKindCons dataName consName) _ _)
          | not (isOpaque opacity),
            Just consNameList <- Map.lookup dataName denv,
            consName `elem` consNameList,
            checkClauseListSanity consNameList clauseList -> do
            let app = (m, TermPiElim e' (resultType : lamList))
            reduceTermPlus app
        _ -> do
          resultType' <- reduceTermPlus resultType
          mSubject' <- mapM reduceTermPlus mSubject
          t' <- reduceTermPlus t
          clauseList' <- forM clauseList $ \((mPat, name, xts), body) -> do
            body' <- reduceTermPlus body
            return ((mPat, name, xts), body')
          return (m, TermCase resultType' mSubject' (e', t') clauseList')
    _ ->
      return term

checkClauseListSanity :: [T.Text] -> [(Pattern, TermPlus)] -> Bool
checkClauseListSanity consNameList clauseList =
  case (consNameList, clauseList) of
    ([], []) ->
      True
    (consName : restConsNameList, ((_, name, _), _) : restClauseList)
      | consName == asText name ->
        checkClauseListSanity restConsNameList restClauseList
    _ ->
      False

toLamList :: Hint -> (Pattern, TermPlus) -> TermPlus
toLamList m ((_, _, xts), body) =
  (m, TermPiIntro OpacityTransparent LamKindNormal xts body)

substTermPlus :: SubstTerm -> TermPlus -> IO TermPlus
substTermPlus sub term =
  case term of
    (_, TermTau) ->
      return term
    (_, TermVar _ x)
      | Just e <- IntMap.lookup (asInt x) sub ->
        return e
      | otherwise ->
        return term
    (m, TermPi xts t) -> do
      (xts', t') <- substTermPlus' sub xts t
      return (m, TermPi xts' t')
    (m, TermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix xt -> do
          (xt' : xts', e') <- substTermPlus' sub (xt : xts) e
          return (m, TermPiIntro opacity (LamKindFix xt') xts' e')
        _ -> do
          (xts', e') <- substTermPlus' sub xts e
          return (m, TermPiIntro opacity kind xts' e')
    (m, TermPiElim e es) -> do
      e' <- substTermPlus sub e
      es' <- mapM (substTermPlus sub) es
      return (m, TermPiElim e' es')
    (_, TermConst _) ->
      return term
    (_, TermInt {}) ->
      return term
    (_, TermFloat {}) ->
      return term
    (_, TermEnum _ _) ->
      return term
    (_, TermEnumIntro _ _) ->
      return term
    (m, TermEnumElim (e, t) branchList) -> do
      t' <- substTermPlus sub t
      e' <- substTermPlus sub e
      let (caseList, es) = unzip branchList
      es' <- mapM (substTermPlus sub) es
      return (m, TermEnumElim (e', t') (zip caseList es'))
    (m, TermDerangement i es) -> do
      es' <- mapM (substTermPlus sub) es
      return (m, TermDerangement i es')
    (m, TermCase resultType mSubject (e, t) clauseList) -> do
      resultType' <- substTermPlus sub resultType
      mSubject' <- mapM (substTermPlus sub) mSubject
      e' <- substTermPlus sub e
      t' <- substTermPlus sub t
      clauseList' <- forM clauseList $ \((mPat, name, xts), body) -> do
        (xts', body') <- substTermPlus' sub xts body
        return ((mPat, name, xts'), body')
      return (m, TermCase resultType' mSubject' (e', t') clauseList')
    (m, TermIgnore e) -> do
      e' <- substTermPlus sub e
      return (m, TermIgnore e')

substTermPlus' ::
  SubstTerm ->
  [IdentPlus] ->
  TermPlus ->
  IO ([IdentPlus], TermPlus)
substTermPlus' sub binder e =
  case binder of
    [] -> do
      e' <- substTermPlus sub e
      return ([], e')
    ((m, x, t) : xts) -> do
      t' <- substTermPlus sub t
      x' <- newIdentFromIdent x
      let sub' = IntMap.insert (asInt x) (m, TermVar VarKindLocal x') sub
      (xts', e') <- substTermPlus' sub' xts e
      return ((m, x', t') : xts', e')
