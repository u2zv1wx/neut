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
polarize (i :< TermProduct v1 v2) = do
  Value v1' <- polarize v1 >>= toValue
  Value v2' <- polarize v2 >>= toValue
  return $ PolarizedTermValue $ Value $ i :< ValueProduct v1' v2'
polarize (i :< TermInject x v) = do
  Value v' <- polarize v >>= toValue
  return $ PolarizedTermValue $ Value $ i :< ValueInject x v'
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
