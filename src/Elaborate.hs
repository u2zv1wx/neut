module Elaborate
  ( elaborate,
  )
where

import Control.Monad.State.Lazy
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.List (nub)
import Data.LowType
import Data.Meta
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
elaborate ss = do
  e <- reduceTermPlus <$> elaborateStmt ss
  p $ T.unpack $ toText $ weaken e
  return e

-- elaborate :: [WeakStmt] -> WithEnv TermPlus
-- elaborate =
--   elaborateStmt

elaborateStmt :: [WeakStmt] -> WithEnv TermPlus
elaborateStmt stmt =
  case stmt of
    [] -> do
      m <- newMeta 1 1 <$> getCurrentFilePath
      return (m, TermInt 64 0)
    WeakStmtLet m (mx, x, t) e : cont -> do
      (e', te) <- infer e
      t' <- inferType t
      insConstraintEnv te t'
      elaborateLet m mx x t' e' cont
    WeakStmtLetWT m (mx, x, t) e : cont -> do
      t' <- inferType t
      elaborateLet m mx x t' e cont
    WeakStmtConstDecl (_, c, t) : cont -> do
      t' <- inferType t
      analyze >> synthesize >> refine >> cleanup
      t'' <- reduceTermPlus <$> elaborate' t'
      insConstTypeEnv c t''
      elaborateStmt cont

-- elaborateStmt :: [WeakStmt] -> WithEnv Stmt
-- elaborateStmt stmt =
--   case stmt of
--     [] ->
--       -- warnUnusedVar
--       StmtReturn . newMeta 1 1 <$> getCurrentFilePath
--     WeakStmtLet m (mx, x, t) e : cont -> do
--       (e', te) <- infer e
--       t' <- inferType t
--       insConstraintEnv te t'
--       elaborateLet m mx x t' e' cont
--     WeakStmtLetWT m (mx, x, t) e : cont -> do
--       (e', te) <- infer e
--       t' <- inferType t
--       insConstraintEnv te t'
--       elaborateLet m mx x t' e' cont
--     -- t' <- inferType t
--     -- elaborateLet m mx x t' e cont
--     WeakStmtConstDecl (_, c, t) : cont -> do
--       t' <- inferType t
--       analyze >> synthesize >> refine >> cleanup
--       t'' <- reduceTermPlus <$> elaborate' t'
--       insConstTypeEnv c t''
--       elaborateStmt cont

elaborateLet ::
  Meta ->
  Meta ->
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
  modify (\env -> env {substEnv = IntMap.insert (asInt x) (weaken e') (substEnv env)})
  modify (\env -> env {defEnv = IntMap.insert (asInt x) e' (defEnv env)})
  cont' <- elaborateStmt cont
  return (m, TermPiElim (m, TermPiIntro [(mx, x, t')] cont') [e'])

-- StmtLet m (mx, x, t') e' <$> elaborateStmt cont

-- elaborateLet ::
--   Meta ->
--   Meta ->
--   Ident ->
--   WeakTermPlus ->
--   WeakTermPlus ->
--   [WeakStmt] ->
--   WithEnv Stmt
-- elaborateLet m mx x t e cont = do
--   analyze >> synthesize >> refine >> cleanup
--   e' <- reduceTermPlus <$> elaborate' e
--   t' <- reduceTermPlus <$> elaborate' t
--   insWeakTypeEnv x $ weaken t'
--   modify (\env -> env {substEnv = IntMap.insert (asInt x) (weaken e') (substEnv env)})
--   modify (\env -> env {defEnv = IntMap.insert (asInt x) e' (defEnv env)})
--   StmtLet m (mx, x, t') e' <$> elaborateStmt cont

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
    (m, WeakTermPiElim (mh, WeakTermHole (I (_, x))) es) -> do
      sub <- gets substEnv
      case IntMap.lookup x sub of
        Nothing ->
          raiseError mh "couldn't instantiate the hole here"
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
    (m, WeakTermHole _) ->
      raiseCritical
        m
        "every meta-variable must be of the form (?M e1 ... en) where n >= 0, but found the meta-variable here that doesn't fit this pattern"
    (m, WeakTermConst x) ->
      return (m, TermConst x)
    (m, WeakTermCall x) ->
      return (m, TermCall x)
    (m, WeakTermInt t x) -> do
      t' <- reduceTermPlus <$> elaborate' t
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
          caseCheckEnumIdent m x $ map snd ls
          return (m, TermEnumElim (e', t') (zip ls es'))
        _ ->
          raiseError m $
            "the type of `"
              <> toText (weaken e')
              <> "` must be an enum type, but is:\n"
              <> toText (weaken t')
    (m, WeakTermArray dom k) -> do
      dom' <- elaborate' dom
      return (m, TermArray dom' k)
    (m, WeakTermArrayIntro k es) -> do
      es' <- mapM elaborate' es
      return (m, TermArrayIntro k es')
    (m, WeakTermArrayElim k xts e1 e2) -> do
      e1' <- elaborate' e1
      xts' <- mapM elaboratePlus xts
      e2' <- elaborate' e2
      return (m, TermArrayElim k xts' e1' e2')
    (m, WeakTermStruct ts) ->
      return (m, TermStruct ts)
    (m, WeakTermStructIntro eks) -> do
      let (es, ks) = unzip eks
      es' <- mapM elaborate' es
      return (m, TermStructIntro $ zip es' ks)
    (m, WeakTermStructElim xts e1 e2) -> do
      e1' <- elaborate' e1
      e2' <- elaborate' e2
      return (m, TermStructElim xts e1' e2')
    (m, WeakTermQuestion e t) -> do
      e' <- elaborate' e
      whenCheck $ do
        t' <- elaborate' t
        note m $ toText (weaken t')
      return e'
    (_, WeakTermErase _ e) ->
      elaborate' e

elaboratePlus :: (Meta, a, WeakTermPlus) -> WithEnv (Meta, a, TermPlus)
elaboratePlus (m, x, t) = do
  t' <- elaborate' t
  return (m, x, t')

caseCheckEnumIdent :: Meta -> T.Text -> [EnumCase] -> WithEnv ()
caseCheckEnumIdent m x ls = do
  es <- lookupEnumSet m x
  caseCheckEnumIdent' m (length es) ls

caseCheckEnumIdent' :: Meta -> Int -> [EnumCase] -> WithEnv ()
caseCheckEnumIdent' m i labelList = do
  let len = length (nub labelList)
  throwIfFalse m $ i <= len || EnumCaseDefault `elem` labelList

throwIfFalse :: Meta -> Bool -> WithEnv ()
throwIfFalse m b =
  if b
    then return ()
    else raiseError m "non-exhaustive pattern"

lookupEnumSet :: Meta -> T.Text -> WithEnv [T.Text]
lookupEnumSet m name = do
  eenv <- gets enumEnv
  case Map.lookup name eenv of
    Nothing ->
      raiseError m $ "no such enum defined: " <> name
    Just xis ->
      return $ map fst xis
-- warnUnusedVar :: WithEnv ()
-- warnUnusedVar =
--   whenCheck $ do
--     set <- gets intactSet
--     let set' = S.map (\(m, x) -> (getPosInfo m, x)) set
--     warnUnusedVar' $ S.toList set'

-- warnUnusedVar' :: [(PosInfo, T.Text)] -> WithEnv ()
-- warnUnusedVar' infoList =
--   case infoList of
--     [] ->
--       return ()
--     ((pos, x) : pxs)
--       | T.all (`S.notMember` S.fromList "()") x -> do
--         warn pos $ "defined but not used: `" <> x <> "`"
--         warnUnusedVar' pxs
--       | otherwise ->
--         warnUnusedVar' pxs
