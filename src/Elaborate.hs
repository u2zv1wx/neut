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
import Data.Term
import qualified Data.Text as T
import Data.WeakTerm
import Elaborate.Infer
import Elaborate.Unify
import Path
import Reduce.Term
import Reduce.WeakTerm

-- elaborate :: [WeakStmtPlus] -> IO [StmtPlus]
elaborate :: ([WeakStmtPlus], WeakStmtPlus) -> IO ([StmtPlus], StmtPlus)
elaborate (ss, mainDefList) =
  case ss of
    [] -> do
      mainDefList' <- elaborateStmtPlus mainDefList
      return ([], mainDefList')
    headStmtPlus : rest -> do
      headStmtPlus' <- elaborateStmtPlus headStmtPlus
      (rest', s') <- elaborate (rest, mainDefList)
      return (headStmtPlus' : rest', s')

elaborateStmtPlus :: WeakStmtPlus -> IO StmtPlus
elaborateStmtPlus (path, defList) = do
  mapM_ (setupDef path) defList
  defList' <- inferStmtList defList
  -- cs <- readIORef constraintEnv
  -- p "==========================================================="
  -- forM_ cs $ \(e1, e2) -> do
  --   p $ T.unpack $ toText e1
  --   p $ T.unpack $ toText e2
  --   p "---------------------"
  unify
  defList'' <- elaborateStmtList path defList'
  return (path, defList'')

setupDef :: Path Abs File -> WeakStmt -> IO ()
setupDef path def =
  case def of
    WeakStmtDef _ x t e -> do
      insWeakTypeEnv x t
      nenv <- readIORef transparentTopNameEnv
      when (Map.member (asText x) nenv) $
        modifyIORef' topDefEnv $ \env -> Map.insert (path, asInt x) e env
    _ ->
      return ()

inferStmtList :: [WeakStmt] -> IO [WeakStmt]
inferStmtList stmtList =
  case stmtList of
    [] ->
      return []
    WeakStmtDef m x t e : rest -> do
      (e', te) <- infer e
      t' <- inferType t
      insConstraintEnv te t'
      when (asText x == "main") $ insConstraintEnv t (m, WeakTermConst "i64")
      rest' <- inferStmtList rest
      return $ WeakStmtDef m x t' e' : rest'
    _ : rest ->
      inferStmtList rest

elaborateStmtList :: Path Abs File -> [WeakStmt] -> IO [Stmt]
elaborateStmtList path stmtList = do
  case stmtList of
    [] ->
      return []
    WeakStmtDef m x t e : rest -> do
      e' <- elaborate' e
      t' <- elaborate' t >>= reduceTermPlus
      insWeakTypeEnv x $ weaken t'
      modifyIORef' topDefEnv $ \env -> Map.insert (path, asInt x) (weaken e') env
      rest' <- elaborateStmtList path rest
      return $ StmtDef m x t' e' : rest'
    _ : rest ->
      elaborateStmtList path rest

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
    (m, WeakTermEnum path k) ->
      return (m, TermEnum path k)
    (m, WeakTermEnumIntro path x) ->
      return (m, TermEnumIntro path x)
    (m, WeakTermEnumElim (e, t) les) -> do
      e' <- elaborate' e
      let (ls, es) = unzip les
      es' <- mapM elaborate' es
      t' <- elaborate' t >>= reduceTermPlus
      case t' of
        (_, TermEnum path x) -> do
          checkSwitchExaustiveness m x (map snd ls)
          checkEnumElim m path $ map snd ls
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
      oenv <- readIORef opaqueTopNameEnv
      case t' of
        (_, TermPiElim (_, TermVar _ name) _)
          | Just bs <- Map.lookup (asText name) denv,
            Map.member (asText name) oenv -> do
            patList' <- elaboratePatternList m bs patList
            return (m, TermCase resultType' mSubject' (e', t') patList')
        (_, TermVar _ name)
          | Just bs <- Map.lookup (asText name) denv,
            Map.member (asText name) oenv -> do
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

checkEnumElim :: Hint -> Path Abs File -> [EnumCase] -> IO ()
checkEnumElim m path ls =
  case ls of
    [] ->
      return ()
    l : rest -> do
      case l of
        EnumCaseLabel fp _
          | fp /= path ->
            raiseError m "enum-elim"
        _ ->
          checkEnumElim m path rest

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
      return $ map fst $ snd xis
