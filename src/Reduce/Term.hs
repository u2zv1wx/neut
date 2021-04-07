module Reduce.Term
  ( reduceTermPlus,
    inlineTermPlus,
    substTermPlus,
    substTermPlus'',
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

type NameEnv = IntMap.IntMap Ident

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
      case e' of
        (_, TermPiIntro opacity LamKindNormal xts body)
          | not (isOpaque opacity),
            length xts == length es' -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            substTermPlus' sub IntMap.empty (m, snd body) >>= reduceTermPlus
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
    -- (m, TermTensor ts) -> do
    --   ts' <- mapM reduceTermPlus ts
    --   return (m, TermTensor ts')
    -- (m, TermTensorIntro es) -> do
    --   es' <- mapM reduceTermPlus es
    --   return (m, TermTensorIntro es')
    -- (m, TermTensorElim xts e1 e2) -> do
    --   e1' <- reduceTermPlus e1
    --   case e1' of
    --     (_, TermTensorIntro es)
    --       | length es == length xts -> do
    --         let xs = map (\(_, x, _) -> asInt x) xts
    --         let sub = IntMap.fromList $ zip xs es
    --         substTermPlus' sub IntMap.empty (m, snd e2) >>= reduceTermPlus
    --     _ -> do
    --       e2' <- reduceTermPlus e2
    --       let (ms, xs, ts) = unzip3 xts
    --       ts' <- mapM reduceTermPlus ts
    --       return (m, TermTensorElim (zip3 ms xs ts') e1' e2')
    (m, TermDerangement i t ekts) -> do
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM reduceTermPlus es
      ts' <- mapM reduceTermPlus ts
      return (m, TermDerangement i t (zip3 es' ks ts'))
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

inlineTermPlus :: TermPlus -> WithEnv TermPlus
inlineTermPlus term =
  case term of
    (m, TermPi xts cod) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM inlineTermPlus ts
      cod' <- inlineTermPlus cod
      return (m, TermPi (zip3 ms xs ts') cod')
    (m, TermPiIntro opacity kind xts e) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM inlineTermPlus ts
      e' <- inlineTermPlus e
      case kind of
        LamKindFix (mx, x, t) -> do
          t' <- inlineTermPlus t
          return (m, TermPiIntro opacity (LamKindFix (mx, x, t')) (zip3 ms xs ts') e')
        _ ->
          return (m, TermPiIntro opacity kind (zip3 ms xs ts') e')
    (m, TermPiElim e es) -> do
      e' <- inlineTermPlus e
      es' <- mapM inlineTermPlus es
      let app = TermPiElim e' es'
      let valueCond = and $ map isValue es
      case e' of
        (_, TermPiIntro opacity LamKindNormal xts body)
          | not (isOpaque opacity),
            length xts == length es',
            valueCond -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            substTermPlus' sub IntMap.empty (m, snd body) >>= inlineTermPlus
        _ ->
          return (m, app)
    (m, TermEnumElim (e, t) les) -> do
      e' <- inlineTermPlus e
      let (ls, es) = unzip les
      es' <- mapM inlineTermPlus es
      let les' = zip ls es'
      let les'' = zip (map snd ls) es'
      t' <- inlineTermPlus t
      case e' of
        (_, TermEnumIntro l) ->
          case lookup (EnumCaseLabel l) les'' of
            Just body ->
              inlineTermPlus (m, snd body)
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body ->
                  inlineTermPlus (m, snd body)
                Nothing ->
                  return (m, TermEnumElim (e', t') les')
        _ ->
          return (m, TermEnumElim (e', t') les')
    -- (m, TermTensor ts) -> do
    --   ts' <- mapM inlineTermPlus ts
    --   return (m, TermTensor ts')
    -- (m, TermTensorIntro es) -> do
    --   es' <- mapM inlineTermPlus es
    --   return (m, TermTensorIntro es')
    -- (m, TermTensorElim xts e1 e2) -> do
    --   e1' <- inlineTermPlus e1
    --   case e1' of
    --     (_, TermTensorIntro es)
    --       | length es == length xts -> do
    --         let xs = map (\(_, x, _) -> asInt x) xts
    --         let sub = IntMap.fromList $ zip xs es
    --         substTermPlus' sub IntMap.empty (m, snd e2) >>= inlineTermPlus
    --     _ -> do
    --       e2' <- inlineTermPlus e2
    --       let (ms, xs, ts) = unzip3 xts
    --       ts' <- mapM inlineTermPlus ts
    --       return (m, TermTensorElim (zip3 ms xs ts') e1' e2')
    (m, TermDerangement i t ekts) -> do
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM inlineTermPlus es
      ts' <- mapM inlineTermPlus ts
      return (m, TermDerangement i t (zip3 es' ks ts'))
    (m, TermCase resultType mSubject (e, t) clauseList) -> do
      e' <- inlineTermPlus e
      let lamList = map (toLamList m) clauseList
      denv <- gets dataEnv
      case e' of
        (_, TermPiIntro opacity (LamKindCons dataName consName) _ _)
          | not (isOpaque opacity),
            Just consNameList <- Map.lookup dataName denv,
            consName `elem` consNameList,
            checkClauseListSanity consNameList clauseList -> do
            let app = (m, TermPiElim e' (resultType : lamList))
            inlineTermPlus app
        _ -> do
          resultType' <- inlineTermPlus resultType
          mSubject' <- mapM inlineTermPlus mSubject
          t' <- inlineTermPlus t
          clauseList' <- forM clauseList $ \((name, xts), body) -> do
            body' <- inlineTermPlus body
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

-- (m, TermPiIntro Nothing xts body)

substTermPlus ::
  SubstTerm ->
  TermPlus ->
  WithEnv TermPlus
substTermPlus sub term =
  substTermPlus' sub IntMap.empty term

substTermPlus' ::
  SubstTerm ->
  NameEnv ->
  TermPlus ->
  WithEnv TermPlus
substTermPlus' sub nenv term =
  case term of
    (_, TermTau) ->
      return term
    (m, TermVar opacity x)
      | Just x' <- IntMap.lookup (asInt x) nenv ->
        return (m, TermVar opacity x')
      | Just e <- IntMap.lookup (asInt x) sub ->
        return e
      | otherwise ->
        return term
    (m, TermPi xts t) -> do
      (xts', t') <- substTermPlus'' sub nenv xts t
      return (m, TermPi xts' t')
    (m, TermPiIntro opacity kind xts e) -> do
      case kind of
        LamKindFix (mx, x, t) -> do
          t' <- substTermPlus' sub nenv t
          x' <- newIdentFromIdent x
          let nenv' = IntMap.insert (asInt x) x' nenv
          (xts', e') <- substTermPlus'' sub nenv' xts e
          return (m, TermPiIntro opacity (LamKindFix (mx, x', t')) xts' e')
        _ -> do
          (xts', e') <- substTermPlus'' sub nenv xts e
          return (m, TermPiIntro opacity kind xts' e')
    (m, TermPiElim e es) -> do
      e' <- substTermPlus' sub nenv e
      es' <- mapM (substTermPlus' sub nenv) es
      return (m, TermPiElim e' es')
    (_, TermConst _) ->
      return term
    (m, TermInt size x) ->
      return (m, TermInt size x)
    (m, TermFloat size x) ->
      return (m, TermFloat size x)
    (m, TermEnum x) ->
      return (m, TermEnum x)
    (m, TermEnumIntro l) ->
      return (m, TermEnumIntro l)
    (m, TermEnumElim (e, t) branchList) -> do
      t' <- substTermPlus' sub nenv t
      e' <- substTermPlus' sub nenv e
      let (caseList, es) = unzip branchList
      es' <- mapM (substTermPlus' sub nenv) es
      return (m, TermEnumElim (e', t') (zip caseList es'))
    -- (m, TermTensor ts) -> do
    --   ts' <- mapM (substTermPlus' sub nenv) ts
    --   return (m, TermTensor ts')
    -- (m, TermTensorIntro es) -> do
    --   es' <- mapM (substTermPlus' sub nenv) es
    --   return (m, TermTensorIntro es')
    -- (m, TermTensorElim xts e1 e2) -> do
    --   e1' <- substTermPlus' sub nenv e1
    --   (xts', e2') <- substTermPlus'' sub nenv xts e2
    --   return (m, TermTensorElim xts' e1' e2')
    (m, TermDerangement i resultType ekts) -> do
      resultType' <- substTermPlus' sub nenv resultType
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM (substTermPlus' sub nenv) es
      ts' <- mapM (substTermPlus' sub nenv) ts
      return (m, TermDerangement i resultType' (zip3 es' ks ts'))
    (m, TermCase resultType mSubject (e, t) clauseList) -> do
      resultType' <- substTermPlus' sub nenv resultType
      mSubject' <- mapM (substTermPlus' sub nenv) mSubject
      e' <- substTermPlus' sub nenv e
      t' <- substTermPlus' sub nenv t
      clauseList' <- forM clauseList $ \((name, xts), body) -> do
        (xts', body') <- substTermPlus'' sub nenv xts body
        return ((name, xts'), body')
      return (m, TermCase resultType' mSubject' (e', t') clauseList')

substTermPlus'' ::
  SubstTerm ->
  NameEnv ->
  [IdentPlus] ->
  TermPlus ->
  WithEnv ([IdentPlus], TermPlus)
substTermPlus'' sub nenv binder e =
  case binder of
    [] -> do
      e' <- substTermPlus' sub nenv e
      return ([], e')
    ((m, x, t) : xts) -> do
      x' <- newIdentFromIdent x
      let nenv' = IntMap.insert (asInt x) x' nenv
      (xts', e') <- substTermPlus'' sub nenv' xts e
      t' <- substTermPlus' sub nenv t
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
