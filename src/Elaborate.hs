module Elaborate
  ( elaborate,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
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
import Data.Time
import Data.WeakTerm
import Elaborate.Analyze
import Elaborate.Infer
import Elaborate.Synthesize
import Numeric
import Reduce.Term
import Reduce.WeakTerm

elaborate :: [WeakStmt] -> WithEnv Stmt
elaborate =
  elaborateStmt

elaborateStmt :: [WeakStmt] -> WithEnv Stmt
elaborateStmt stmt =
  case stmt of
    [] -> do
      warnUnusedVar
      StmtReturn . newMeta 1 1 <$> getCurrentFilePath
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
    WeakStmtVerify m e : cont -> do
      whenCheck $ do
        (e', _) <- infer e
        e'' <- elaborate' e'
        start <- liftIO getCurrentTime
        _ <- normalize e''
        stop <- liftIO getCurrentTime
        let sec = realToFrac $ diffUTCTime stop start
        note m $ "verification succeeded (" <> T.pack (showFloat' sec) <> " seconds)"
      elaborateStmt cont
    WeakStmtImplicit x is : cont -> do
      ienv <- gets impEnv
      modify (\env -> env {impEnv = IntMap.insertWith (++) (asInt x) is ienv})
      elaborateStmt cont

elaborateLet ::
  Meta ->
  Meta ->
  Ident ->
  WeakTermPlus ->
  WeakTermPlus ->
  [WeakStmt] ->
  WithEnv Stmt
elaborateLet m mx x t e cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate' e
  t' <- reduceTermPlus <$> elaborate' t
  insWeakTypeEnv x $ weaken t'
  modify (\env -> env {substEnv = IntMap.insert (asInt x) (weaken e') (substEnv env)})
  modify (\env -> env {defEnv = IntMap.insert (asInt x) e' (defEnv env)})
  StmtLet m (mx, x, t') e' <$> elaborateStmt cont

cleanup :: WithEnv ()
cleanup =
  modify (\env -> env {constraintEnv = []})

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})

showFloat' :: Float -> String
showFloat' x =
  showFFloat Nothing x ""

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
    (m, WeakTermPi mName xts t) -> do
      xts' <- mapM elaboratePlus xts
      t' <- elaborate' t
      return (m, TermPi mName xts' t')
    (m, WeakTermPiIntro info xts e) -> do
      xts' <- mapM elaboratePlus xts
      e' <- elaborate' e
      case info of
        Nothing ->
          return (m, TermPiIntro Nothing xts' e')
        Just (indName, consName, args) -> do
          args' <- mapM elaboratePlus args
          return (m, TermPiIntro (Just (indName, consName, args')) xts' e')
    (m, WeakTermPiElim (mh, WeakTermHole (I (_, x))) es) -> do
      sub <- gets substEnv
      case IntMap.lookup x sub of
        Nothing ->
          raiseError mh "couldn't instantiate the hole here"
        Just (_, WeakTermPiIntro _ xts e)
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
    (m, WeakTermIter (mx, x, t) xts e) -> do
      t' <- elaborate' t
      xts' <- mapM elaboratePlus xts
      e' <- elaborate' e
      return (m, TermIter (mx, x, t') xts' e')
    (m, WeakTermHole _) ->
      raiseCritical
        m
        "every meta-variable must be of the form (?M e1 ... en) where n >= 0, but found the meta-variable here that doesn't fit this pattern"
    (m, WeakTermConst x) ->
      return (m, TermConst x)
    (m, WeakTermBoxElim x) ->
      return (m, TermBoxElim x)
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
    (m, WeakTermCase mIndName e cxtes) -> do
      e' <- elaborate' e
      cxtes' <-
        forM cxtes $ \((c, xts), body) -> do
          xts' <- mapM elaboratePlus xts
          body' <- elaborate' body
          return ((c, xts'), body')
      eenv <- gets enumEnv
      case cxtes' of
        [] ->
          case mIndName of
            Nothing ->
              return (m, TermCase Nothing e' cxtes') -- ex falso quodlibet
            Just indName ->
              raiseError m $ "the inductive type `" <> asText indName <> "` is not a bottom-type"
        _ ->
          case mIndName of
            Nothing ->
              raiseCritical m undefined
            Just indName ->
              case Map.lookup (asText indName) eenv of
                Nothing -> raiseError m $ "no such inductive type defined: " <> asText indName
                Just bis -> do
                  let bs' = map (snd . fst . fst) cxtes
                  let isLinear = linearCheck bs'
                  let isExhaustive = length bis == length bs'
                  case (isLinear, isExhaustive) of
                    (False, _) ->
                      raiseError m "found a non-linear pattern"
                    (_, False) ->
                      raiseError m "found a non-exhaustive pattern"
                    (True, True) ->
                      return (m, TermCase (Just indName) e' cxtes')
    (m, WeakTermQuestion e t) -> do
      e' <- elaborate' e
      whenCheck $ do
        t' <- elaborate' t
        case (getArgLen t', isUpsilonOrConst e') of
          (Just len, True) -> do
            (is, e'') <- getImpInfo e'
            let form = toText (weaken e'') : showFormArgs 0 is [0 .. len - 1]
            let formStr = inParen $ showItems form
            note m $ toText (weaken t') <> "\n-\n" <> formStr
          _ ->
            note m $ toText (weaken t')
      return e'
    (_, WeakTermErase _ e) ->
      elaborate' e

isUpsilonOrConst :: TermPlus -> Bool
isUpsilonOrConst term =
  case term of
    (_, TermUpsilon _) ->
      True
    (_, TermConst _) ->
      True
    _ ->
      False

getImpInfo :: TermPlus -> WithEnv ([Int], TermPlus)
getImpInfo term =
  case term of
    (m, TermUpsilon x)
      | not (metaIsExplicit m) -> do
        ienv <- gets impEnv
        case IntMap.lookup (asInt x) ienv of
          Just is ->
            return (is, term)
          Nothing ->
            return ([], term)
      | otherwise ->
        return ([], (m, TermUpsilon (I ("@" <> asText x, asInt x))))
    _ ->
      return ([], term)

getArgLen :: TermPlus -> Maybe Int
getArgLen term =
  case term of
    (_, TermPi _ xts _) ->
      return $ length xts
    _ ->
      Nothing

showFormArgs :: Int -> [Int] -> [Int] -> [T.Text]
showFormArgs k impList idxList =
  case idxList of
    [] ->
      []
    [i]
      | i `elem` impList ->
        ["*"]
      | otherwise ->
        ["#" <> T.pack (show k)]
    (i : is)
      | i `elem` impList ->
        "*" : showFormArgs k impList is
      | otherwise ->
        "#" <> T.pack (show k) : showFormArgs (k + 1) impList is

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

warnUnusedVar :: WithEnv ()
warnUnusedVar =
  whenCheck $ do
    set <- gets intactSet
    let set' = S.map (\(m, x) -> (getPosInfo m, x)) set
    warnUnusedVar' $ S.toList set'

warnUnusedVar' :: [(PosInfo, T.Text)] -> WithEnv ()
warnUnusedVar' infoList =
  case infoList of
    [] ->
      return ()
    ((pos, x) : pxs)
      | T.all (`S.notMember` S.fromList "()") x -> do
        warn pos $ "defined but not used: `" <> x <> "`"
        warnUnusedVar' pxs
      | otherwise ->
        warnUnusedVar' pxs
