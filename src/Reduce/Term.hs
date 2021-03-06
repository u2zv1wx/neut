module Reduce.Term
  ( reduceTermPlus,
    substTermPlus,
    substTermPlus'',
  )
where

import Data.Basic
import Data.Env
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
    (m, TermPiIntro xts e) -> do
      let (ms, xs, ts) = unzip3 xts
      ts' <- mapM reduceTermPlus ts
      e' <- reduceTermPlus e
      return (m, TermPiIntro (zip3 ms xs ts') e')
    (m, TermPiElim e es) -> do
      e' <- reduceTermPlus e
      es' <- mapM reduceTermPlus es
      let app = TermPiElim e' es'
      let valueCond = and $ map isValue es
      case e' of
        (mLam, TermPiIntro xts body)
          | length xts == length es',
            metaIsReducible mLam,
            valueCond -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es'
            substTermPlus' sub IntMap.empty body >>= reduceTermPlus
        _ ->
          return (m, app)
    (m, TermFix (mx, x, t) xts e)
      | x `notElem` varTermPlus e ->
        reduceTermPlus (m, TermPiIntro xts e)
      | otherwise -> do
        t' <- reduceTermPlus t
        e' <- reduceTermPlus e
        let (ms, xs, ts) = unzip3 xts
        ts' <- mapM reduceTermPlus ts
        return (m, TermFix (mx, x, t') (zip3 ms xs ts') e')
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
              reduceTermPlus body
            Nothing ->
              case lookup EnumCaseDefault les'' of
                Just body ->
                  reduceTermPlus body
                Nothing ->
                  return (m, TermEnumElim (e', t') les')
        _ ->
          return (m, TermEnumElim (e', t') les')
    (m, TermTensor ts) -> do
      ts' <- mapM reduceTermPlus ts
      return (m, TermTensor ts')
    (m, TermTensorIntro es) -> do
      es' <- mapM reduceTermPlus es
      return (m, TermTensorIntro es')
    (m, TermTensorElim xts e1 e2) -> do
      e1' <- reduceTermPlus e1
      case e1' of
        (_, TermTensorIntro es)
          | length es == length xts -> do
            let xs = map (\(_, x, _) -> asInt x) xts
            let sub = IntMap.fromList $ zip xs es
            substTermPlus' sub IntMap.empty e2 >>= reduceTermPlus
        _ -> do
          e2' <- reduceTermPlus e2
          let (ms, xs, ts) = unzip3 xts
          ts' <- mapM reduceTermPlus ts
          return (m, TermTensorElim (zip3 ms xs ts') e1' e2')
    (m, TermDerangement i t ekts) -> do
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM reduceTermPlus es
      ts' <- mapM reduceTermPlus ts
      return (m, TermDerangement i t (zip3 es' ks ts'))
    _ ->
      return term

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
    (m, TermUpsilon x)
      | Just e <- IntMap.lookup (asInt x) sub ->
        return e
      | Just x' <- IntMap.lookup (asInt x) nenv ->
        return (m, TermUpsilon x')
      | otherwise ->
        return term
    (m, TermPi xts t) -> do
      (xts', t') <- substTermPlus'' sub nenv xts t
      return (m, TermPi xts' t')
    (m, TermPiIntro xts body) -> do
      (xts', body') <- substTermPlus'' sub nenv xts body
      return (m, TermPiIntro xts' body')
    (m, TermPiElim e es) -> do
      e' <- substTermPlus' sub nenv e
      es' <- mapM (substTermPlus' sub nenv) es
      return (m, TermPiElim e' es')
    (m, TermFix (mx, x, t) xts e) -> do
      t' <- substTermPlus' sub nenv t
      let sub' = IntMap.delete (asInt x) sub
      x' <- newNameWith x
      let nenv' = IntMap.insert (asInt x) x' nenv
      (xts', e') <- substTermPlus'' sub' nenv' xts e
      return (m, TermFix (mx, x', t') xts' e')
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
    (m, TermTensor ts) -> do
      ts' <- mapM (substTermPlus' sub nenv) ts
      return (m, TermTensor ts')
    (m, TermTensorIntro es) -> do
      es' <- mapM (substTermPlus' sub nenv) es
      return (m, TermTensorIntro es')
    (m, TermTensorElim xts e1 e2) -> do
      e1' <- substTermPlus' sub nenv e1
      (xts', e2') <- substTermPlus'' sub nenv xts e2
      return (m, TermTensorElim xts' e1' e2')
    (m, TermDerangement i resultType ekts) -> do
      resultType' <- substTermPlus' sub nenv resultType
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM (substTermPlus' sub nenv) es
      ts' <- mapM (substTermPlus' sub nenv) ts
      return (m, TermDerangement i resultType' (zip3 es' ks ts'))

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
      let sub' = IntMap.delete (asInt x) sub
      x' <- newNameWith x
      let nenv' = IntMap.insert (asInt x) x' nenv
      (xts', e') <- substTermPlus'' sub' nenv' xts e
      t' <- substTermPlus' sub nenv t
      return ((m, x', t') : xts', e')

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
