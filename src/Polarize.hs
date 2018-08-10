module Polarize where

import           Control.Monad

import           Control.Comonad.Cofree

import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import           Pattern

polarize :: WeakTerm -> WithEnv Term
polarize (Meta {ident = i} :< WeakTermVar s) = do
  t <- findTypeV i
  return $ TermValue $ Value $ VMeta {vtype = t} :< ValueVar s
polarize (Meta {ident = i} :< WeakTermNodeApp s []) = do
  t <- findTypeV i
  return $ TermValue $ Value $ VMeta {vtype = t} :< ValueNodeApp s []
polarize (Meta {ident = i} :< WeakTermNodeApp s vs) = do
  t <- findTypeV i
  let sanitizer v =
        case v of
          TermValue (Value v) -> return v
          _ -> lift $ throwE $ "the polarity of " ++ show v ++ " is wrong"
  vs' <- mapM polarize vs
  vs'' <- mapM sanitizer vs'
  return $ TermValue $ Value $ VMeta {vtype = t} :< ValueNodeApp s vs''
polarize (Meta {ident = i} :< WeakTermLam (s, _) e) = do
  t <- findTypeC i
  mc <- polarize e
  case mc of
    TermComp (Comp c) ->
      return $ TermComp $ Comp $ CMeta {ctype = t} :< CompLam s c
    _ -> lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"
polarize (Meta {ident = i} :< WeakTermApp e1 e2) = do
  t <- findTypeC i
  mc <- polarize e1
  mv <- polarize e2
  case (mc, mv) of
    (TermComp (Comp c), TermValue v) ->
      return $ TermComp $ Comp $ CMeta {ctype = t} :< CompApp c v
    _ ->
      lift $
      throwE $ "the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (Meta {ident = i} :< WeakTermRet e) = do
  t <- findTypeC i
  mv <- polarize e
  case mv of
    TermValue v -> return $ TermComp $ Comp $ CMeta {ctype = t} :< CompRet v
    _ -> lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"
polarize (Meta {ident = i} :< WeakTermBind (s, _) e1 e2) = do
  t <- findTypeC i
  mc1 <- polarize e1
  mc2 <- polarize e2
  case (mc1, mc2) of
    (TermComp (Comp c1), TermComp (Comp c2)) ->
      return $ TermComp $ Comp $ CMeta {ctype = t} :< CompBind s c1 c2
    _ ->
      lift $
      throwE $
      "foo the polarity of " ++ show e1 ++ " or " ++ show e2 ++ " is wrong"
polarize (Meta {ident = i} :< WeakTermThunk e) = do
  t <- findTypeV i
  mc <- polarize e
  case mc of
    TermComp c ->
      return $ TermValue $ Value $ VMeta {vtype = t} :< ValueThunk c i
    _ -> lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"
polarize (Meta {ident = i} :< WeakTermUnthunk e) = do
  t <- findTypeC i
  mv <- polarize e
  case mv of
    TermValue v ->
      return $ TermComp $ Comp $ CMeta {ctype = t} :< CompUnthunk v i
    _ -> lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"
polarize (Meta {ident = i} :< WeakTermMu (s, _) e) = do
  t <- findTypeC i
  mc <- polarize e
  case mc of
    TermComp (Comp c) ->
      return $ TermComp $ Comp $ CMeta {ctype = t} :< CompMu s c
    _ -> lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"
polarize (Meta {ident = i} :< WeakTermCase vs ves) = do
  t <- findTypeC i
  ves' <-
    forM ves $ \(v, e) -> do
      e' <- polarize e
      case e' of
        TermComp (Comp c) -> return (v, c)
        _ ->
          lift $
          throwE $
          "the polarity of " ++ show v ++ " or " ++ show e ++ " is wrong"
  vs' <- mapM polarize vs
  let sanitizer v =
        case v of
          TermValue (Value v) -> return $ Value v
          _ -> lift $ throwE $ "the polarity of " ++ show v ++ " is wrong"
  vs'' <- mapM sanitizer vs'
  -- create a decision tree from the pattern
  let vesMod = patDist ves'
  liftIO $ putStrLn $ Pr.ppShow vesMod
  let initialOccurences = map (const []) vs
  decisionTree <- toDecision initialOccurences vesMod
  return $ TermComp $ Comp $ CMeta {ctype = t} :< CompCase vs'' decisionTree
polarize (_ :< WeakTermAsc e _) = polarize e

polarizeType :: WeakType -> WithEnv Type
polarizeType (WeakTypeVar i) = return $ TypeValueType (ValueTypeVar i)
polarizeType (WeakTypeNode x ts) = do
  let sanitizer v =
        case v of
          TypeValueType v -> return v
          _ -> lift $ throwE $ "the polarity of " ++ show v ++ " is wrong"
  ts' <- mapM polarizeType ts
  ts'' <- mapM sanitizer ts'
  return $ TypeValueType $ ValueTypeNode x ts''
polarizeType (WeakTypeUp t) = do
  mt' <- polarizeType t
  case mt' of
    TypeValueType t' -> return $ TypeCompType (CompTypeUp t')
    _ -> lift $ throwE $ "the polarity of " ++ show t ++ " is wrong"
polarizeType (WeakTypeDown t _) = do
  mt' <- polarizeType t
  case mt' of
    TypeCompType t' -> return $ TypeValueType (ValueTypeDown t')
    _ -> lift $ throwE $ "the polarity of " ++ show t ++ " is wrong"
polarizeType (WeakTypeUniv (WeakLevelFixed i)) =
  return $ TypeValueType (ValueTypeUniv i)
polarizeType (WeakTypeUniv (WeakLevelHole _)) =
  return $ TypeValueType (ValueTypeUniv 0) -- for now
polarizeType (WeakTypeForall (Ident s, t1) t2) = do
  mt1' <- polarizeType t1
  mt2' <- polarizeType t2
  case (mt1', mt2') of
    (TypeValueType t1', TypeCompType t2') ->
      return $ TypeCompType (CompTypeForall (s, t1') t2')
    _ ->
      lift $
      throwE $ "the polarity of " ++ show t1 ++ " or " ++ show t2 ++ " is wrong"
polarizeType (WeakTypeForall (Hole i, t1) t2) = do
  mt1' <- polarizeType t1
  mt2' <- polarizeType t2
  case (mt1', mt2') of
    (TypeValueType t1', TypeCompType t2') ->
      return $ TypeCompType (CompTypeForall (i, t1') t2')
    _ ->
      lift $
      throwE $ "the polarity of " ++ show t1 ++ " or " ++ show t2 ++ " is wrong"
polarizeType t = lift $ throwE $ "the polarity of " ++ show t ++ " is wrong"

polarizeTypeArg :: [(Identifier, WeakType)] -> WithEnv [(Identifier, ValueType)]
polarizeTypeArg [] = return []
polarizeTypeArg ((i, wt):wts) = do
  mwt' <- polarizeType wt
  wts' <- polarizeTypeArg wts
  case mwt' of
    TypeValueType wt' -> return $ (i, wt') : wts'
    _ -> lift $ throwE $ "the polarity of " ++ show wt ++ " is wrong"

polarizeTypeEnv :: [(Identifier, WeakType)] -> WithEnv [(Identifier, Type)]
polarizeTypeEnv [] = return []
polarizeTypeEnv ((i, wt):ts) = do
  wt' <- polarizeType wt
  ts' <- polarizeTypeEnv ts
  return $ (i, wt') : ts'

findTypeV :: Identifier -> WithEnv ValueType
findTypeV s = do
  t <- lookupWTEnv' s
  t' <- polarizeType t
  case t' of
    TypeValueType vt -> return vt
    TypeCompType _ ->
      lift $ throwE $ "The polarity of " ++ show s ++ " is wrong"

findTypeC :: Identifier -> WithEnv CompType
findTypeC s = do
  t <- lookupWTEnv' s
  t' <- polarizeType t
  case t' of
    TypeCompType ct -> return ct
    TypeValueType _ ->
      lift $ throwE $ "The polarity of " ++ show s ++ " is wrong"
