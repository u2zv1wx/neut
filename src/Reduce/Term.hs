module Reduce.Term
  ( reduceTermPlus,
    substTermPlus,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Namespace
import Data.Term
import qualified Data.Text as T

reduceTermPlus :: TermPlus -> WithEnv TermPlus
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
      let valueCond = and $ map isValue es
      case e' of
        (_, TermPiIntro opacity LamKindNormal xts body)
          | not (isOpaque opacity),
            length xts == length es',
            valueCond -> do
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
        (_, TermEnumIntro l) ->
          case lookup (EnumCaseLabel l) les'' of
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
      denv <- gets dataEnv
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
          clauseList' <- forM clauseList $ \((name, xts), body) -> do
            body' <- reduceTermPlus body
            return ((name, xts), body')
          return (m, TermCase resultType' mSubject' (e', t') clauseList')
    _ ->
      return term

checkClauseListSanity :: [T.Text] -> [(Pattern, TermPlus)] -> Bool
checkClauseListSanity consNameList clauseList =
  case (consNameList, clauseList) of
    ([], []) ->
      True
    (consName : restConsNameList, ((name, _), _) : restClauseList)
      | consName == asText name ->
        checkClauseListSanity restConsNameList restClauseList
    _ ->
      False

toLamList :: Hint -> (Pattern, TermPlus) -> TermPlus
toLamList m ((_, xts), body) =
  (m, TermPiIntro OpacityTransparent LamKindNormal xts body)

substTermPlus :: SubstTerm -> TermPlus -> WithEnv TermPlus
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
    (_, TermEnum _) ->
      return term
    (_, TermEnumIntro _) ->
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
      clauseList' <- forM clauseList $ \((name, xts), body) -> do
        (xts', body') <- substTermPlus' sub xts body
        return ((name, xts'), body')
      return (m, TermCase resultType' mSubject' (e', t') clauseList')

substTermPlus' ::
  SubstTerm ->
  [IdentPlus] ->
  TermPlus ->
  WithEnv ([IdentPlus], TermPlus)
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

isValue :: TermPlus -> Bool
isValue term =
  case term of
    (_, TermTau) ->
      True
    (_, TermVar _ _) ->
      True
    (_, TermPi {}) ->
      True
    (_, TermPiIntro {}) ->
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
    _ ->
      False

isValueConst :: T.Text -> Bool
isValueConst x
  | Just _ <- asLowTypeMaybe x =
    True
  | Just _ <- asPrimOp x =
    True
  | x == "os" <> nsSep <> "stdin" =
    True
  | x == "os" <> nsSep <> "stdout" =
    True
  | x == "os" <> nsSep <> "stderr" =
    True
  | otherwise =
    False
