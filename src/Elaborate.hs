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
import Elaborate.Infer
import Elaborate.Unify
import Reduce.Term
import Reduce.WeakTerm

elaborate :: [WeakStmt] -> WithEnv [Stmt]
elaborate ss =
  elaborateStmt' ss

elaborateStmt' :: [WeakStmt] -> WithEnv [Stmt]
elaborateStmt' stmt =
  case stmt of
    [] -> do
      return []
    WeakStmtDef m (mx, x, t) e : cont -> do
      (e', te) <- infer e
      t' <- inferType t
      insConstraintEnv te t'
      -- cs <- gets constraintEnv
      -- p "==========================================================="
      -- forM_ cs $ \(e1, e2) -> do
      --   p $ T.unpack $ toText e1
      --   p $ T.unpack $ toText e2
      --   p "---------------------"
      unify
      e'' <- elaborate' e' >>= inlineTermPlus
      t'' <- elaborate' t' >>= reduceTermPlus
      insWeakTypeEnv x $ weaken t''
      modify (\env -> env {substEnv = IntMap.insert (asInt x) (weaken e'') (substEnv env)})
      cont' <- elaborateStmt' cont
      return $ StmtDef m (mx, x, t'') e'' : cont'
    WeakStmtResourceType m name discarder copier : cont -> do
      insConstTypeEnv name (m, TermTau)
      (discarder', tDiscarder) <- infer discarder
      (copier', tCopier) <- infer copier
      let tPtr = (m, WeakTermEnum (nsUnsafe <> "pointer"))
      h <- newIdentFromText "res"
      insConstraintEnv (m, WeakTermPi [(m, h, tPtr)] (m, WeakTermTensor [])) tDiscarder
      insConstraintEnv (m, WeakTermPi [(m, h, tPtr)] tPtr) tCopier
      unify
      discarder'' <- elaborate' discarder' >>= inlineTermPlus
      copier'' <- elaborate' copier' >>= inlineTermPlus
      cont' <- elaborateStmt' cont
      return $ StmtResourceType m name discarder'' copier'' : cont'
    WeakStmtOpaque name : cont -> do
      modify (\env -> env {opaqueEnv = S.insert name (opaqueEnv env)})
      elaborateStmt' cont

elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' term =
  case term of
    (m, WeakTermTau) ->
      return (m, TermTau)
    (m, WeakTermVar opacity x) -> do
      cset <- gets constantSet
      let x' = asText x
      if S.member x' cset
        then return (m, TermConst x')
        else return (m, TermVar opacity x)
    (m, WeakTermPi xts t) -> do
      xts' <- mapM elaborateWeakIdentPlus xts
      t' <- elaborate' t
      return (m, TermPi xts' t')
    (m, WeakTermPiIntro isReducible kind xts e) -> do
      kind' <- elaborateKind kind
      xts' <- mapM elaborateWeakIdentPlus xts
      e' <- elaborate' e
      return (m, TermPiIntro isReducible kind' xts' e')
    (m, WeakTermPiElim (mh, WeakTermAster x) es) -> do
      sub <- gets substEnv
      case IntMap.lookup x sub of
        Nothing -> do
          p' term
          raiseError mh "couldn't instantiate the asterisk here"
        Just (_, WeakTermPiIntro OpacityTransparent LamKindNormal xts e)
          | length xts == length es -> do
            let xs = map (\(_, y, _) -> asInt y) xts
            let s = IntMap.fromList $ zip xs es
            substWeakTermPlus s e >>= elaborate'
        Just e ->
          reduceWeakTermPlus (m, WeakTermPiElim e es) >>= elaborate'
    (m, WeakTermPiElim e es) -> do
      e' <- elaborate' e
      es' <- mapM elaborate' es
      return (m, TermPiElim e' es')
    (m, WeakTermAster _) ->
      raiseCritical m "every meta-variable must be of the form (?M e1 ... en) where n >= 0, but the meta-variable here doesn't fit this pattern"
    (m, WeakTermConst x) ->
      return (m, TermConst x)
    (m, WeakTermInt t x) -> do
      t' <- elaborate' t >>= reduceTermPlus
      case t' of
        (_, TermConst intTypeStr)
          | Just (LowTypeInt size) <- asLowTypeMaybe intTypeStr ->
            return (m, TermInt size x)
        _ ->
          raiseError m $
            "the term `"
              <> T.pack (show x)
              <> "` is an integer, but its type is: "
              <> toText (weaken t')
    (m, WeakTermFloat t x) -> do
      t' <- elaborate' t >>= reduceTermPlus
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
      t' <- elaborate' t >>= reduceTermPlus
      case t' of
        (_, TermEnum x) -> do
          checkSwitchExaustiveness m x (map snd ls)
          return (m, TermEnumElim (e', t') (zip ls es'))
        _ ->
          raiseError m $
            "the type of `"
              <> toText (weaken e')
              <> "` must be an enum type, but is:\n"
              <> toText (weaken t')
    (m, WeakTermTensor ts) -> do
      ts' <- mapM elaborate' ts
      return (m, TermTensor ts')
    (m, WeakTermTensorIntro es) -> do
      es' <- mapM elaborate' es
      return (m, TermTensorIntro es')
    (m, WeakTermTensorElim xts e1 e2) -> do
      xts' <- mapM elaborateWeakIdentPlus xts
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
      ts' <- mapM (elaborate' >=> reduceTermPlus) ts
      return (m, TermDerangement i resultType' (zip3 es' ks ts'))
    (m, WeakTermCase resultType mSubject (e, t) patList) -> do
      resultType' <- elaborate' resultType
      mSubject' <- mapM elaborate' mSubject
      e' <- elaborate' e
      t' <- elaborate' t >>= reduceTermPlus
      patList' <- forM patList $ \((c, xts), body) -> do
        xts' <- mapM elaborateWeakIdentPlus xts
        body' <- elaborate' body
        return ((c, xts'), body')
      denv <- gets dataEnv
      oenv <- gets opaqueEnv
      case t' of
        (_, TermPiElim (_, TermVar _ name) _)
          | Just bs <- Map.lookup (asText name) denv,
            S.member name oenv -> do
            let bs' = map (\((b, _), _) -> asText b) patList
            forM_ (zip bs bs') $ \(b, b') -> do
              if b == b'
                then return ()
                else raiseError m $ "the constructor here is supposed to be `" <> b <> "`, but is: `" <> b' <> "`" -- fixme: add hint for patterns
            return (m, TermCase resultType' mSubject' (e', t') patList')
        _ -> do
          raiseError (fst t) $ "the type of this term must be a data-type, but its type is:\n" <> toText (weaken t')

elaborateWeakIdentPlus :: WeakIdentPlus -> WithEnv IdentPlus
elaborateWeakIdentPlus (m, x, t) = do
  t' <- elaborate' t
  return (m, x, t')

elaborateKind :: LamKind WeakIdentPlus -> WithEnv (LamKind IdentPlus)
elaborateKind kind =
  case kind of
    LamKindNormal ->
      return LamKindNormal
    LamKindCons t1 t2 ->
      return $ LamKindCons t1 t2
    LamKindFix xt -> do
      xt' <- elaborateWeakIdentPlus xt
      return $ LamKindFix xt'

checkSwitchExaustiveness :: Hint -> T.Text -> [EnumCase] -> WithEnv ()
checkSwitchExaustiveness m x caseList = do
  let b = EnumCaseDefault `elem` caseList
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
