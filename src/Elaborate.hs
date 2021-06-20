module Elaborate
  ( elaborate,
  )
where

import Control.Monad
import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import qualified Data.IntMap as IntMap
import Data.List (nub)
import Data.Log
import Data.LowType
import qualified Data.Set as S
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Infer
import Elaborate.Unify
import Reduce.Term
import Reduce.WeakTerm

elaborate :: [WeakStmt] -> IO [Stmt]
elaborate ss =
  elaborateStmt' ss

elaborateStmt' :: [WeakStmt] -> IO [Stmt]
elaborateStmt' stmt =
  case stmt of
    [] -> do
      return []
    WeakStmtDef m mx t e : cont -> do
      (e', te) <- infer e
      t' <- inferType t
      insConstraintEnv te t'
      -- cs <- readIORef constraintEnv
      -- p "==========================================================="
      -- forM_ cs $ \(e1, e2) -> do
      --   p $ T.unpack $ toText e1
      --   p $ T.unpack $ toText e2
      --   p "---------------------"
      unify
      e'' <- elaborate' e'
      t'' <- elaborate' t' >>= reduceTermPlus
      case mx of
        Just (isReducible, x) -> do
          insWeakTypeEnv x $ weaken t''
          modifyIORef' substEnv $ \env -> IntMap.insert (asInt x) (weaken e'') env
          when (not isReducible) $
            modifyIORef' opaqueEnv $ \env -> S.insert x env
          cont' <- elaborateStmt' cont
          return $ StmtDef m (Just x) t'' e'' : cont'
        Nothing -> do
          cont' <- elaborateStmt' cont
          return $ StmtDef m Nothing t'' e'' : cont'

elaborate' :: WeakTermPlus -> IO TermPlus
elaborate' term =
  case term of
    (m, WeakTermTau) ->
      return (m, TermTau)
    (m, WeakTermVar opacity x) ->
      return (m, TermVar opacity x)
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
      sub <- readIORef substEnv
      case IntMap.lookup x sub of
        Nothing ->
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
    (m, WeakTermQuestion e t) -> do
      e' <- elaborate' e
      t' <- elaborate' t
      note m $ toText (weaken t')
      return e'
    (m, WeakTermDerangement i es) -> do
      es' <- mapM elaborate' es
      return (m, TermDerangement i es')
    (m, WeakTermCase resultType mSubject (e, t) patList) -> do
      resultType' <- elaborate' resultType
      mSubject' <- mapM elaborate' mSubject
      e' <- elaborate' e
      t' <- elaborate' t >>= reduceTermPlus
      denv <- readIORef dataEnv
      oenv <- readIORef opaqueEnv
      case t' of
        (_, TermPiElim (_, TermVar _ name) _)
          | Just bs <- Map.lookup (asText name) denv,
            S.member name oenv -> do
            patList' <- elaboratePatternList m bs patList
            return (m, TermCase resultType' mSubject' (e', t') patList')
        (_, TermVar _ name)
          | Just bs <- Map.lookup (asText name) denv,
            S.member name oenv -> do
            patList' <- elaboratePatternList m bs patList
            return (m, TermCase resultType' mSubject' (e', t') patList')
        _ -> do
          raiseError (fst t) $ "the type of this term must be a data-type, but its type is:\n" <> (toText $ weaken t')
    (m, WeakTermIgnore e) -> do
      e' <- elaborate' e
      return (m, TermIgnore e')

-- for now
elaboratePatternList :: Hint -> [T.Text] -> [(WeakPattern, WeakTermPlus)] -> IO [(Pattern, TermPlus)]
elaboratePatternList m bs patList = do
  patList' <- forM patList $ \((mPat, c, xts), body) -> do
    xts' <- mapM elaborateWeakIdentPlus xts
    body' <- elaborate' body
    return ((mPat, c, xts'), body')
  checkCaseSanity m bs patList'
  return patList'

checkCaseSanity :: Hint -> [T.Text] -> [(Pattern, TermPlus)] -> IO ()
checkCaseSanity m bs patList =
  case (bs, patList) of
    ([], []) ->
      return ()
    (b : bsRest, ((mPat, b', _), _) : patListRest) -> do
      if b /= asText b'
        then raiseError mPat $ "the constructor here is supposed to be `" <> b <> "`, but is: `" <> asText b' <> "`"
        else checkCaseSanity m bsRest patListRest
    (b : _, []) ->
      raiseError m $ "found a non-exhaustive pattern; the clause for `" <> b <> "` is missing"
    ([], ((mPat, b, _), _) : _) ->
      raiseError mPat $ "found a redundant pattern; this clause for `" <> asText b <> "` is redundant"

elaborateWeakIdentPlus :: WeakIdentPlus -> IO IdentPlus
elaborateWeakIdentPlus (m, x, t) = do
  t' <- elaborate' t
  return (m, x, t')

elaborateKind :: LamKind WeakIdentPlus -> IO (LamKind IdentPlus)
elaborateKind kind =
  case kind of
    LamKindNormal ->
      return LamKindNormal
    LamKindCons t1 t2 ->
      return $ LamKindCons t1 t2
    LamKindFix xt -> do
      xt' <- elaborateWeakIdentPlus xt
      return $ LamKindFix xt'
    LamKindResourceHandler ->
      return LamKindResourceHandler

checkSwitchExaustiveness :: Hint -> T.Text -> [EnumCase] -> IO ()
checkSwitchExaustiveness m x caseList = do
  let b = EnumCaseDefault `elem` caseList
  enumSet <- lookupEnumSet m x
  let len = toInteger $ length (nub caseList)
  when (not ((toInteger (length enumSet)) <= len || b)) $
    raiseError m "this switch is ill-constructed in that it is not exhaustive"

lookupEnumSet :: Hint -> T.Text -> IO [T.Text]
lookupEnumSet m name = do
  eenv <- readIORef enumEnv
  case Map.lookup name eenv of
    Nothing ->
      raiseError m $ "no such enum defined: " <> name
    Just xis ->
      return $ map fst xis
