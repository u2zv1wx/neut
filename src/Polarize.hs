module Polarize where

import           Control.Monad

import           Control.Comonad.Cofree

import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import           Pattern

polarize :: Term -> WithEnv PolarizedTerm
polarize (i :< TermVar s) =
  return $ PolarizedTermValue $ Value $ i :< ValueVar s
polarize (i :< TermConst s) =
  return $ PolarizedTermValue $ Value $ i :< ValueConst s
polarize (i :< TermLam s e) = do
  Comp c <- polarize e >>= toComp
  return $ PolarizedTermComp $ Comp $ i :< CompLam s c
polarize (i :< TermApp e1 e2) = do
  Comp c <- polarize e1 >>= toComp
  v <- polarize e2 >>= toValue
  return $ PolarizedTermComp $ Comp $ i :< CompApp c v
polarize (i :< TermLift e) = do
  v <- polarize e >>= toValue
  return $ PolarizedTermComp $ Comp $ i :< CompLift v
polarize (i :< TermBind s e1 e2) = do
  Comp c1 <- polarize e1 >>= toComp
  Comp c2 <- polarize e2 >>= toComp
  return $ PolarizedTermComp $ Comp $ i :< CompBind s c1 c2
polarize (i :< TermThunk e) = do
  c <- polarize e >>= toComp
  return $ PolarizedTermValue $ Value $ i :< ValueThunk c
polarize (i :< TermUnthunk e) = do
  v <- polarize e >>= toValue
  return $ PolarizedTermComp $ Comp $ i :< CompUnthunk v
polarize (i :< TermMu s e) = do
  Comp c <- polarize e >>= toComp
  return $ PolarizedTermComp $ Comp $ i :< CompMu s c
polarize (i :< TermCase vs ves) = do
  ves' <- polarizeClause ves
  vs' <- mapM polarize vs >>= mapM toValue
  let vesMod = patDist ves'
  let indexList = map (const []) vs
  let metaList = map (\(meta :< _) -> meta) vs
  typeList <- mapM lookupTypeEnv' metaList
  let initialOccurences = zip indexList typeList
  decisionTree <- toDecision initialOccurences vesMod
  return $ PolarizedTermComp $ Comp $ i :< CompDecision vs' decisionTree

toValue :: PolarizedTerm -> WithEnv Value
toValue (PolarizedTermValue (Value c)) = return $ Value c
toValue e = lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"

toComp :: PolarizedTerm -> WithEnv Comp
toComp (PolarizedTermComp (Comp c)) = return $ Comp c
toComp e = lift $ throwE $ "the polarity of " ++ show e ++ " is wrong"

polarizeClause :: [([Pat], Term)] -> WithEnv [([Pat], PreComp)]
polarizeClause [] = return []
polarizeClause ((patList, e):ves) = do
  e' <- polarize e
  Comp c <- toComp e'
  ves' <- polarizeClause ves
  return $ (patList, c) : ves'
-- polarizeType :: Type -> WithEnv PolarizedType
-- polarizeType (Fix (TypeVar i)) =
--   return $ PolarizedTypeValueType (ValueTypeVar i)
-- polarizeType (Fix (TypeHole i)) =
--   return $ PolarizedTypeValueType (ValueTypeVar i)
-- polarizeType (Fix (TypeNode x ts)) = do
--   let sanitizer v =
--         case v of
--           PolarizedTypeValueType v -> return v
--           _ -> lift $ throwE $ "the polarity of " ++ show v ++ " is wrong"
--   ts' <- mapM polarizeType ts
--   ts'' <- mapM sanitizer ts'
--   return $ PolarizedTypeCompType $ CompTypeNode x ts''
-- polarizeType (Fix (TypeUp t)) = do
--   mt' <- polarizeType t
--   case mt' of
--     PolarizedTypeValueType t' -> return $ PolarizedTypeCompType (CompTypeUp t')
--     _ -> lift $ throwE $ "the polarity of " ++ show t ++ " is wrong"
-- polarizeType (Fix (TypeDown t)) = do
--   mt' <- polarizeType t
--   case mt' of
--     PolarizedTypeCompType t' ->
--       return $ PolarizedTypeValueType (ValueTypeDown t')
--     _ -> lift $ throwE $ "the polarity of " ++ show t ++ " is wrong"
-- polarizeType (Fix (TypeUniv (WeakLevelFixed i))) =
--   return $ PolarizedTypeValueType (ValueTypeUniv i)
-- polarizeType (Fix (TypeUniv (WeakLevelHole _))) =
--   return $ PolarizedTypeValueType (ValueTypeUniv 0) -- for now
-- polarizeType (Fix (TypeForall (s, t1) t2)) = do
--   mt1' <- polarizeType t1
--   mt2' <- polarizeType t2
--   case (mt1', mt2') of
--     (PolarizedTypeValueType t1', PolarizedTypeCompType t2') ->
--       return $ PolarizedTypeCompType (CompTypeForall (s, t1') t2')
--     _ ->
--       lift $
--       throwE $ "the polarity of " ++ show t1 ++ " or " ++ show t2 ++ " is wrong"
-- polarizeType t = lift $ throwE $ "the polarity of " ++ show t ++ " is wrong"
-- polarizeTypeArg :: [(Identifier, Type)] -> WithEnv [(Identifier, ValueType)]
-- polarizeTypeArg [] = return []
-- polarizeTypeArg ((i, wt):wts) = do
--   mwt' <- polarizeType wt
--   wts' <- polarizeTypeArg wts
--   case mwt' of
--     PolarizedTypeValueType wt' -> return $ (i, wt') : wts'
--     _ -> lift $ throwE $ "the polarity of " ++ show wt ++ " is wrong"
-- -- polarizeTypeEnv :: [(Identifier, Type)] -> WithEnv ()
-- -- polarizeTypeEnv [] = return ()
-- -- polarizeTypeEnv ((i, wt):ts) = do
-- --   wt' <- polarizeType wt
-- --   case wt' of
-- --     PolarizedTypeCompType ct  -> insCTEnv i ct
-- --     PolarizedTypeValueType vt -> insVTEnv i vt
-- --   polarizeTypeEnv ts
