module Elaborate
  ( elaborate,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.List (nub)
import Data.Log
import Data.LowType
import Data.Namespace
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize
import Reduce.Term
import Reduce.WeakTerm

elaborate :: [WeakStmt] -> WithEnv TermPlus
elaborate ss =
  reduceTermPlus <$> elaborateStmt ss

elaborateStmt :: [WeakStmt] -> WithEnv TermPlus
elaborateStmt stmt =
  case stmt of
    [] -> do
      ph <- gets phase
      m <- newHint ph 1 1 <$> getCurrentFilePath
      return (m, TermInt 64 0)
    WeakStmtLet m (mx, x, t) e : cont -> do
      (e', te) <- infer e
      t' <- inferType t
      insConstraintEnv te t'
      elaborateLet m mx x t' e' cont
    WeakStmtConstDecl (_, c, t) : cont -> do
      t' <- inferType t
      analyze >> synthesize >> refine >> cleanup
      t'' <- reduceTermPlus <$> elaborate' t'
      insConstTypeEnv c t''
      elaborateStmt cont
    WeakStmtResourceType m name discarder copier : cont -> do
      insConstTypeEnv name (m, TermTau)
      (discarder', tDiscarder) <- infer discarder
      (copier', tCopier) <- infer copier
      let tPtr = (m, WeakTermConst (nsUnsafe <> "pointer"))
      h <- newNameWith' "res"
      insConstraintEnv tDiscarder (m, WeakTermPi [(m, h, tPtr)] (m, WeakTermTensor []))
      insConstraintEnv tCopier (m, WeakTermPi [(m, h, tPtr)] (m, WeakTermTensor [tPtr, tPtr]))
      analyze >> synthesize >> refine >> cleanup
      discarder'' <- reduceTermPlus <$> elaborate' discarder'
      copier'' <- reduceTermPlus <$> elaborate' copier'
      modify (\env -> env {resTypeEnv = Map.insert name (discarder'', copier'') (resTypeEnv env)})
      elaborateStmt cont

elaborateLet ::
  Hint ->
  Hint ->
  Ident ->
  WeakTermPlus ->
  WeakTermPlus ->
  [WeakStmt] ->
  WithEnv TermPlus
elaborateLet m mx x t e cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate' e
  t' <- reduceTermPlus <$> elaborate' t
  insWeakTypeEnv x $ weaken t'
  if metaIsReducible m
    then modify (\env -> env {substEnv = IntMap.insert (asInt x) (weaken e') (substEnv env)})
    else modify (\env -> env {opaqueEnv = S.insert x (opaqueEnv env)})
  cont' <- elaborateStmt cont
  return (m, TermPiElim (m, TermPiIntro [(mx, x, t')] cont') [e'])

cleanup :: WithEnv ()
cleanup =
  modify (\env -> env {constraintEnv = []})

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})

elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' term =
  case term of
    (m, WeakTermTau) ->
      return (m, TermTau)
    (m, WeakTermUpsilon x) -> do
      cset <- gets constantSet
      let x' = asText x
      if S.member x' cset
        then return (m, TermConst x')
        else return (m, TermUpsilon x)
    (m, WeakTermPi xts t) -> do
      xts' <- mapM elaboratePlus xts
      t' <- elaborate' t
      return (m, TermPi xts' t')
    (m, WeakTermPiIntro xts e) -> do
      xts' <- mapM elaboratePlus xts
      e' <- elaborate' e
      return (m, TermPiIntro xts' e')
    (m, WeakTermPiElim (mh, WeakTermAster x) es) -> do
      sub <- gets substEnv
      case IntMap.lookup x sub of
        Nothing ->
          raiseError mh "couldn't instantiate the asterisk here"
        Just (_, WeakTermPiIntro xts e)
          | length xts == length es -> do
            let xs = map (\(_, y, _) -> asInt y) xts
            let s = IntMap.fromList $ zip xs es
            elaborate' $ substWeakTermPlus s e
        Just e ->
          elaborate' $ reduceWeakTermPlus (m, WeakTermPiElim e es)
    (m, WeakTermPiElim e es) -> do
      e' <- elaborate' e
      es' <- mapM elaborate' es
      return (m, TermPiElim e' es')
    (m, WeakTermFix (mx, x, t) xts e) -> do
      t' <- elaborate' t
      xts' <- mapM elaboratePlus xts
      e' <- elaborate' e
      return (m, TermFix (mx, x, t') xts' e')
    (m, WeakTermAster _) ->
      raiseCritical m "every meta-variable must be of the form (?M e1 ... en) where n >= 0, but the meta-variable here doesn't fit this pattern"
    (m, WeakTermConst x) ->
      return (m, TermConst x)
    (m, WeakTermInt t x) -> do
      t' <- reduceTermPlus <$> elaborate' t
      case t' of
        (_, TermEnum intTypeStr)
          | Just (LowTypeInt size) <- asLowTypeMaybe intTypeStr ->
            return (m, TermInt size x)
        _ ->
          raiseError m $
            "the term `"
              <> T.pack (show x)
              <> "` is an integer, but its type is: "
              <> toText (weaken t')
    (m, WeakTermFloat t x) -> do
      t' <- reduceTermPlus <$> elaborate' t
      case t' of
        (_, TermConst floatTypeStr)
          | Just (LowTypeFloat size) <- asLowTypeMaybe floatTypeStr ->
            return (m, TermFloat size x)
        _ ->
          raiseError m $
            "the term `"
              <> T.pack (show x)
              <> "` is a float, but its type is:\n"
              <> toText (weaken t')
    (m, WeakTermEnum k) ->
      return (m, TermEnum k)
    (m, WeakTermEnumIntro x) ->
      return (m, TermEnumIntro x)
    (m, WeakTermEnumElim (e, t) les) -> do
      e' <- elaborate' e
      let (ls, es) = unzip les
      es' <- mapM elaborate' es
      t' <- reduceTermPlus <$> elaborate' t
      case t' of
        (_, TermEnum x) -> do
          checkSwitchExaustiveness m x (map snd ls)
          return (m, TermEnumElim (e', t') (zip ls es'))
        _ ->
          raiseError m $
            "the type of `"
              <> toText (weaken e')
              <> "` must be an enum type or an integer type, but is:\n"
              <> toText (weaken t')
    (m, WeakTermTensor ts) -> do
      ts' <- mapM elaborate' ts
      return (m, TermTensor ts')
    (m, WeakTermTensorIntro es) -> do
      es' <- mapM elaborate' es
      return (m, TermTensorIntro es')
    (m, WeakTermTensorElim xts e1 e2) -> do
      xts' <- mapM elaboratePlus xts
      e1' <- elaborate' e1
      e2' <- elaborate' e2
      return (m, TermTensorElim xts' e1' e2')
    (m, WeakTermQuestion e t) -> do
      e' <- elaborate' e
      t' <- elaborate' t
      note m $ toText (weaken t')
      return e'
    (m, WeakTermDerangement i resultType ekts) -> do
      resultType' <- elaborate' resultType
      let (es, ks, ts) = unzip3 ekts
      es' <- mapM elaborate' es
      ts' <- map reduceTermPlus <$> mapM elaborate' ts
      return (m, TermDerangement i resultType' (zip3 es' ks ts'))

elaboratePlus :: (Hint, a, WeakTermPlus) -> WithEnv (Hint, a, TermPlus)
elaboratePlus (m, x, t) = do
  t' <- elaborate' t
  return (m, x, t')

checkSwitchExaustiveness :: Hint -> T.Text -> [EnumCase] -> WithEnv ()
checkSwitchExaustiveness m x caseList = do
  let b = EnumCaseDefault `elem` caseList
  case asLowInt x of
    Just _ ->
      when (not b) $
        raiseError m "this integer-switch is ill-constructed in that it does not contain `default`"
    Nothing -> do
      enumSet <- lookupEnumSet m x
      let len = toInteger $ length (nub caseList)
      when (not ((toInteger (length enumSet)) <= len || b)) $
        raiseError m "this switch here is ill-constructed in that it is not exhaustive"

lookupEnumSet :: Hint -> T.Text -> WithEnv [T.Text]
lookupEnumSet m name = do
  eenv <- gets enumEnv
  case Map.lookup name eenv of
    Nothing ->
      raiseError m $ "no such enum defined: " <> name
    Just xis ->
      return $ map fst xis

insConstTypeEnv :: T.Text -> TermPlus -> WithEnv ()
insConstTypeEnv x t =
  modify (\e -> e {constTypeEnv = Map.insert x t (constTypeEnv e)})
