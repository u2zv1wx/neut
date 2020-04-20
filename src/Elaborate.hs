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
import Data.Term
import qualified Data.Text as T
import Data.Time
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize
import Numeric
import Reduce.Term
import Reduce.WeakTerm

elaborate :: [WeakStmt] -> WithEnv Stmt
elaborate = elaborateStmt

elaborateStmt :: [WeakStmt] -> WithEnv Stmt
elaborateStmt =
  \case
    [] -> do
      path <- getCurrentFilePath
      let m = newMeta 1 1 path
      return $ StmtReturn m
    WeakStmtLet m (mx, x, t) e : cont -> do
      (e', te) <- infer e
      t' <- inferType t
      insConstraintEnv te t'
      analyze >> synthesize >> refine >> cleanup
      e'' <- reduceTermPlus <$> elaborate' e'
      t'' <- reduceTermPlus <$> elaborate' t'
      insWeakTypeEnv x $ weaken t''
      modify (\env -> env {substEnv = IntMap.insert (asInt x) (weaken e'') (substEnv env)})
      cont' <- elaborateStmt cont
      return $ StmtLet m (mx, x, t'') e'' cont'
    WeakStmtLetWT m (mx, x, t) e : cont -> do
      t' <- inferType t
      analyze >> synthesize >> refine >> cleanup
      e' <- reduceTermPlus <$> elaborate' e -- `e` is supposed to be well-typed
      t'' <- reduceTermPlus <$> elaborate' t'
      insWeakTypeEnv x $ weaken t''
      modify (\env -> env {substEnv = IntMap.insert (asInt x) (weaken e') (substEnv env)})
      cont' <- elaborateStmt cont
      return $ StmtLet m (mx, x, t'') e' cont'
    WeakStmtConstDecl (_, c, t) : cont -> do
      t' <- reduceTermPlus <$> elaborate' t
      insTypeEnv (Right c) t'
      elaborateStmt cont
    WeakStmtVerify m e : cont -> do
      whenCheck $ do
        (e', _) <- infer e
        e'' <- elaborate' e'
        start <- liftIO getCurrentTime
        _ <- normalize e''
        stop <- liftIO getCurrentTime
        let sec = realToFrac $ diffUTCTime stop start :: Float
        note m $
          "verification succeeded (" <> T.pack (showFloat' sec) <> " seconds)"
      elaborateStmt cont

-- elaborateStmt (WeakStmtLetWT m (mx, x, t) e cont) = do
--   t' <- inferType t
--   analyze >> synthesize >> refine >> cleanup
--   e' <- reduceTermPlus <$> elaborate' e -- `e` is supposed to be well-typed
--   t'' <- reduceTermPlus <$> elaborate' t'
--   -- insTypeEnv (Right x) t''
--   insTypeEnv (Left $ asInt x) t''
--   modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
--   cont' <- elaborateStmt cont
--   x' <- newNameWith'' "_"
--   return (m, TermPiElim (m, termPiIntro [(mx, x', t'')] cont') [e'])
-- elaborateStmt (WeakStmtVerify m e cont) = do
--   whenCheck $ do
--     (e', _) <- infer e
--     e'' <- elaborate' e'
--     start <- liftIO $ getCurrentTime
--     _ <- normalize e''
--     stop <- liftIO $ getCurrentTime
--     let sec = realToFrac $ diffUTCTime stop start :: Float
--     note m $
--       "verification succeeded (" <> T.pack (showFloat' sec) <> " seconds)"
--   elaborateStmt cont
-- elaborateStmt (WeakStmtConstDecl _ (_, x, t) cont) = do
--   t' <- inferType t
--   analyze >> synthesize >> refine >> cleanup
--   t'' <- reduceTermPlus <$> elaborate' t'
--   insTypeEnv (Right x) t''
--   elaborateStmt cont

-- elaborateStmt (WeakStmtLet m (mx, x, t) e cont) = do
--   (e', te) <- infer e
--   t' <- inferType t
--   insConstraintEnv te t'
--   analyze >> synthesize >> refine >> cleanup
--   e'' <- reduceTermPlus <$> elaborate' e'
--   t'' <- reduceTermPlus <$> elaborate' t'
--   insTypeEnv (Left $ asInt x) t''
--   -- insTypeEnv (Right x) t''
--   modify (\env -> env {cacheEnv = Map.insert x (Left e'') (cacheEnv env)})
--   cont' <- elaborateStmt cont
--   x' <- newNameWith'' "_"
--   return (m, TermPiElim (m, termPiIntro [(mx, x', t'')] cont') [e''])
-- elaborateStmt (WeakStmtLetWT m (mx, x, t) e cont) = do
--   t' <- inferType t
--   analyze >> synthesize >> refine >> cleanup
--   e' <- reduceTermPlus <$> elaborate' e -- `e` is supposed to be well-typed
--   t'' <- reduceTermPlus <$> elaborate' t'
--   -- insTypeEnv (Right x) t''
--   insTypeEnv (Left $ asInt x) t''
--   modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
--   cont' <- elaborateStmt cont
--   x' <- newNameWith'' "_"
--   return (m, TermPiElim (m, termPiIntro [(mx, x', t'')] cont') [e'])
-- elaborateStmt (WeakStmtVerify m e cont) = do
--   whenCheck $ do
--     (e', _) <- infer e
--     e'' <- elaborate' e'
--     start <- liftIO $ getCurrentTime
--     _ <- normalize e''
--     stop <- liftIO $ getCurrentTime
--     let sec = realToFrac $ diffUTCTime stop start :: Float
--     note m $
--       "verification succeeded (" <> T.pack (showFloat' sec) <> " seconds)"
--   elaborateStmt cont
-- elaborateStmt (WeakStmtConstDecl _ (_, x, t) cont) = do
--   t' <- inferType t
--   analyze >> synthesize >> refine >> cleanup
--   t'' <- reduceTermPlus <$> elaborate' t'
--   insTypeEnv (Right x) t''
--   elaborateStmt cont

-- elaborateStmt (WeakStmtVisit _ ss1 ss2) = do
--   e1 <- elaborateStmt ss1
--   e2 <- elaborateStmt ss2
--   h <- newNameWith'' "_"
--   let m = fst e1
--   return
--     ( m,
--       TermPiElim
--         (m, termPiIntro [(m, h, (m, TermEnum (EnumTypeIntS 64)))] e2)
--         [e1]
--     )

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = IntMap.empty})
  modify (\env -> env {zetaEnv = IntMap.empty})

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})

showFloat' :: Float -> String
showFloat' x = showFFloat Nothing x ""

elaborate' :: WeakTermPlus -> WithEnv TermPlus
elaborate' (m, WeakTermTau) = return (m, TermTau)
elaborate' (m, WeakTermUpsilon x) = return (m, TermUpsilon x)
elaborate' (m, WeakTermPi mName xts t) = do
  xts' <- mapM elaboratePlus xts
  t' <- elaborate' t
  return (m, TermPi mName xts' t')
elaborate' (m, WeakTermPiIntro info xts e) = do
  info' <- fmap2M (mapM elaboratePlus) info
  xts' <- mapM elaboratePlus xts
  e' <- elaborate' e
  return (m, TermPiIntro info' xts' e')
elaborate' (m, WeakTermPiElim (mh, WeakTermZeta (I (_, x))) es) = do
  sub <- gets substEnv
  case IntMap.lookup x sub of
    Nothing -> raiseError mh "couldn't instantiate the hole here"
    Just (_, WeakTermPiIntro _ xts e)
      | length xts == length es -> do
        let xs = map (\(_, y, _) -> Left $ asInt y) xts
        let s = Map.fromList $ zip xs es
        elaborate' $ substWeakTermPlus s e
    Just e -> elaborate' $ reduceWeakTermPlus (m, WeakTermPiElim e es)
elaborate' (m, WeakTermPiElim e es) = do
  e' <- elaborate' e
  es' <- mapM elaborate' es
  return (m, TermPiElim e' es')
elaborate' (m, WeakTermIter (mx, x, t) xts e) = do
  t' <- elaborate' t
  xts' <- mapM elaboratePlus xts
  e' <- elaborate' e
  return (m, TermIter (mx, x, t') xts' e')
elaborate' (m, WeakTermZeta _) =
  raiseCritical
    m
    "every meta-variable must be of the form (?M e1 ... en) where n >= 0, but found the meta-variable here that doesn't fit this pattern"
elaborate' (m, WeakTermConst x) = return (m, TermConst x)
elaborate' (m, WeakTermInt t x) = do
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermEnum (EnumTypeIntS size))
      | (-1) * (2 ^ (size - 1)) <= x,
        x < 2 ^ size ->
        return (m, TermEnumIntro (EnumValueIntS size x))
      | otherwise ->
        raiseError m $
          "the signed integer "
            <> T.pack (show x)
            <> " is inferred to be of type i"
            <> T.pack (show size)
            <> ", but is out of range of i"
            <> T.pack (show size)
    (_, TermEnum (EnumTypeIntU size))
      | 0 <= x,
        x < 2 ^ size ->
        return (m, TermEnumIntro (EnumValueIntU size x))
      | otherwise ->
        raiseError m $
          "the unsigned integer "
            <> T.pack (show x)
            <> " is inferred to be of type u"
            <> T.pack (show size)
            <> ", but is out of range of u"
            <> T.pack (show size)
    _ ->
      raiseError m $
        "the term `"
          <> T.pack (show x)
          <> "` is an integer, but its type is: "
          <> toText (weaken t')
elaborate' (m, WeakTermFloat t x) = do
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermConst floatType)
      | Just (LowTypeFloat size) <- asLowTypeMaybe floatType ->
        return (m, TermFloat size x)
    _ ->
      raiseError m $
        "the term `"
          <> T.pack (show x)
          <> "` is a float, but its type is:\n"
          <> toText (weaken t')
elaborate' (m, WeakTermEnum k) = return (m, TermEnum k)
elaborate' (m, WeakTermEnumIntro x) = return (m, TermEnumIntro x)
elaborate' (m, WeakTermEnumElim (e, t) les) = do
  e' <- elaborate' e
  let (ls, es) = unzip les
  ls' <- mapM elaborateWeakCase ls
  es' <- mapM elaborate' es
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermEnum x) -> do
      caseCheckEnumIdent m x $ map snd ls'
      return (m, TermEnumElim (e', t') (zip ls' es'))
    _ ->
      raiseError m $
        "the type of `"
          <> toText (weaken e')
          <> "` must be an enum type, but is:\n"
          <> toText (weaken t')
elaborate' (m, WeakTermArray dom k) = do
  dom' <- elaborate' dom
  return (m, TermArray dom' k)
elaborate' (m, WeakTermArrayIntro k es) = do
  es' <- mapM elaborate' es
  return (m, TermArrayIntro k es')
elaborate' (m, WeakTermArrayElim k xts e1 e2) = do
  e1' <- elaborate' e1
  xts' <- mapM elaboratePlus xts
  e2' <- elaborate' e2
  return (m, TermArrayElim k xts' e1' e2')
elaborate' (m, WeakTermStruct ts) = return (m, TermStruct ts)
elaborate' (m, WeakTermStructIntro eks) = do
  let (es, ks) = unzip eks
  es' <- mapM elaborate' es
  return (m, TermStructIntro $ zip es' ks)
elaborate' (m, WeakTermStructElim xts e1 e2) = do
  e1' <- elaborate' e1
  e2' <- elaborate' e2
  return (m, TermStructElim xts e1' e2')
elaborate' (m, WeakTermCase indName e cxtes) = do
  e' <- elaborate' e
  cxtes' <-
    forM cxtes $ \((c, xts), body) -> do
      xts' <- mapM elaboratePlus xts
      body' <- elaborate' body
      return ((c, xts'), body')
  eenv <- gets enumEnv
  case cxtes' of
    [] ->
      case Map.lookup indName eenv of
        Nothing -> raiseError m $ "no such inductive type defined: " <> indName
        Just [] -> return (m, TermCase indName e' cxtes')
        Just _ ->
          raiseError m $
            "the inductive type `" <> indName <> "` is not a bottom-type"
    _ ->
      case Map.lookup indName eenv of
        Nothing -> raiseError m $ "no such inductive type defined: " <> indName
        Just bis -> do
          let bs' = map (snd . fst . fst) cxtes
          let isLinear = linearCheck bs'
          let isExhaustive = length bis == length bs'
          case (isLinear, isExhaustive) of
            (False, _) -> raiseError m "found a non-linear pattern"
            (_, False) -> raiseError m "found a non-exhaustive pattern"
            (True, True) -> return (m, TermCase indName e' cxtes')
elaborate' (m, WeakTermQuestion e t) = do
  e' <- elaborate' e
  whenCheck $ do
    t' <- elaborate' t
    case (getArgLen t', isUpsilonOrConst e') of
      (Just len, True) -> do
        let form = toText (weaken e') : showFormArgs 0 [0 .. len - 1]
        let formStr = inParen $ showItems form
        note m $ toText (weaken t') <> "\n-\n" <> formStr
      _ -> note m $ toText (weaken t')
  return e'
elaborate' (_, WeakTermErase _ e) = elaborate' e

isUpsilonOrConst :: TermPlus -> Bool
isUpsilonOrConst (_, TermUpsilon _) = True
isUpsilonOrConst (_, TermConst _) = True
isUpsilonOrConst _ = False

getArgLen :: TermPlus -> Maybe Int
getArgLen (_, TermPi _ xts _) = return $ length xts
getArgLen _ = Nothing

showFormArgs :: Int -> [Int] -> [T.Text]
showFormArgs _ [] = []
showFormArgs k [_] = ["#" <> T.pack (show k)]
showFormArgs k (_ : is) = "#" <> T.pack (show k) : showFormArgs (k + 1) is

elaborateWeakCase :: WeakCasePlus -> WithEnv CasePlus
elaborateWeakCase (m, WeakCaseInt t x) = do
  t' <- reduceTermPlus <$> elaborate' t
  case t' of
    (_, TermEnum (EnumTypeIntS size)) ->
      return (m, CaseValue (EnumValueIntS size x))
    (_, TermEnum (EnumTypeIntU size)) ->
      return (m, CaseValue (EnumValueIntU size x))
    (_, TermEnum (EnumTypeLabel "bool")) ->
      return (m, CaseValue (EnumValueIntS 1 x))
    _ ->
      raiseError m $
        "the type of `"
          <> T.pack (show x)
          <> "` must be an integer type, but is: "
          <> toText (weaken t')
elaborateWeakCase (m, WeakCaseLabel l) =
  return (m, CaseValue $ EnumValueLabel l)
elaborateWeakCase (m, WeakCaseIntS t a) =
  return (m, CaseValue $ EnumValueIntS t a)
elaborateWeakCase (m, WeakCaseIntU t a) =
  return (m, CaseValue $ EnumValueIntU t a)
elaborateWeakCase (m, WeakCaseDefault) = return (m, CaseDefault)

elaboratePlus :: (Meta, a, WeakTermPlus) -> WithEnv (Meta, a, TermPlus)
elaboratePlus (m, x, t) = do
  t' <- elaborate' t
  return (m, x, t')

caseCheckEnumIdent :: Meta -> EnumType -> [Case] -> WithEnv ()
caseCheckEnumIdent m (EnumTypeLabel x) ls = do
  es <- lookupEnumSet m x
  caseCheckEnumIdent' m (length es) ls
caseCheckEnumIdent m (EnumTypeIntS _) ls =
  throwIfFalse m $ CaseDefault `elem` ls
caseCheckEnumIdent m (EnumTypeIntU _) ls =
  throwIfFalse m $ CaseDefault `elem` ls

caseCheckEnumIdent' :: Meta -> Int -> [Case] -> WithEnv ()
caseCheckEnumIdent' m i labelList = do
  let len = length (nub labelList)
  throwIfFalse m $ i <= len || CaseDefault `elem` labelList

throwIfFalse :: Meta -> Bool -> WithEnv ()
throwIfFalse m b =
  if b
    then return ()
    else raiseError m "non-exhaustive pattern"

lookupEnumSet :: Meta -> T.Text -> WithEnv [T.Text]
lookupEnumSet m name = do
  eenv <- gets enumEnv
  case Map.lookup name eenv of
    Nothing -> raiseError m $ "no such enum defined: " <> name
    Just xis -> return $ map fst xis
