module Rename where

import           Control.Monad.State
import           Control.Monad.Trans.Except

import           Control.Comonad.Cofree

import           Data

renameV :: Value -> WithEnv Value
renameV (Value (i :< ValueVar s)) = do
  t <- ValueVar <$> lookupNameEnv s
  return $ Value (i :< t)
renameV (Value (i :< ValueNodeApp s [])) =
  return $ Value (i :< ValueNodeApp s [])
renameV (Value (i :< ValueNodeApp s vs)) = do
  vs' <- mapM (renameV . Value) vs
  let vs'' = map unwrapValue vs'
  return $ Value (i :< ValueNodeApp s vs'')
renameV (Value (i :< ValueThunk e)) = do
  e' <- renameC e
  return $ Value (i :< ValueThunk e')

renameC :: Comp -> WithEnv Comp
renameC (Comp (i :< CompLam s e)) = do
  local $ do
    s' <- newNameWith s
    Comp e' <- renameC $ Comp e
    return $ Comp (i :< CompLam s' e')
renameC (Comp (i :< CompApp e v)) = do
  Comp e' <- renameC $ Comp e
  v' <- renameV v
  return $ Comp (i :< CompApp e' v')
renameC (Comp (i :< CompRet v)) = do
  v' <- renameV v
  return $ Comp (i :< CompRet v')
renameC (Comp (i :< CompBind s e1 e2)) = do
  Comp e1' <- renameC $ Comp e1
  s' <- newNameWith s
  Comp e2' <- renameC $ Comp e2
  return $ Comp (i :< CompBind s' e1' e2')
renameC (Comp (i :< CompUnthunk v)) = do
  v' <- renameV v
  return $ Comp (i :< CompUnthunk v')
renameC (Comp (i :< CompMu s e)) = do
  local $ do
    s' <- newNameWith s
    Comp e' <- renameC $ Comp e
    return $ Comp (i :< CompMu s' e')
renameC (Comp (i :< CompCase vs dtree)) = do
  vs' <- mapM renameV vs
  dtree' <- renameDecision dtree
  return $ Comp (i :< CompCase vs' dtree')

renameDecision :: Decision PreComp -> WithEnv (Decision PreComp)
renameDecision (DecisionLeaf oxs comp) = do
  local $ do
    let (os, xs) = unzip oxs
    xs' <- forM xs $ \x -> newNameWith x
    Comp comp' <- renameC $ Comp comp
    return $ DecisionLeaf (zip os xs') comp'
renameDecision (DecisionSwitch o condDecisionList Nothing) = do
  let (condList, decisionList) = unzip condDecisionList
  decisionList' <- mapM (local . renameDecision) decisionList
  return $ DecisionSwitch o (zip condList decisionList') Nothing
renameDecision (DecisionSwitch o condDecisionList (Just (Nothing, dcase))) = do
  let (condList, decisionList) = unzip condDecisionList
  decisionList' <- mapM (local . renameDecision) decisionList
  dcase' <- renameDecision dcase
  return $
    DecisionSwitch o (zip condList decisionList') (Just (Nothing, dcase'))
renameDecision (DecisionSwitch o condDecisionList (Just (Just d, dcase))) = do
  let (condList, decisionList) = unzip condDecisionList
  decisionList' <- mapM (local . renameDecision) decisionList
  local $ do
    d' <- newNameWith d
    dcase' <- renameDecision dcase
    return $
      DecisionSwitch o (zip condList decisionList') (Just (Just d', dcase'))
renameDecision (DecisionSwap i d) = do
  d' <- renameDecision d
  return $ DecisionSwap i d'

-- renameC (i :< CompAsc e t) = do
--   e' <- renameC e
--   t' <- renameCType t
--   return (i :< CompAsc e' t')
renameType :: WeakType -> WithEnv WeakType
renameType (WeakTypeVar s) = WeakTypeVar <$> lookupNameEnv s
renameType (WeakTypePosHole i) = return (WeakTypePosHole i)
renameType (WeakTypeNegHole i) = return (WeakTypeNegHole i)
renameType (WeakTypeUp t) = WeakTypeUp <$> renameType t
renameType (WeakTypeDown t i) = do
  t' <- renameType t
  return $ WeakTypeDown t' i
renameType (WeakTypeUniv level) = return (WeakTypeUniv level)
renameType (WeakTypeForall (Ident s, tdom) tcod) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- renameType tcod
    return (WeakTypeForall (Ident s', tdom') tcod')
renameType (WeakTypeForall (Hole s, tdom) tcod) = do
  tdom' <- renameType tdom
  local $ do
    s' <- newNameWith s
    tcod' <- renameType tcod
    return (WeakTypeForall (Hole s', tdom') tcod')
renameType (WeakTypeNode s ts) = do
  ts' <- mapM renameType ts
  return $ WeakTypeNode s ts'

renameNodeType ::
     [(Identifier, WeakType)]
  -> WeakType
  -> WithEnv ([(Identifier, WeakType)], WeakType)
renameNodeType [] t = do
  t' <- renameType t
  return ([], t')
renameNodeType ((i, wt):wts) t = do
  wt' <- renameType wt
  local $ do
    i' <- newNameWith i
    (wts', t') <- renameNodeType wts t
    return ((i', wt') : wts', t')

renamePat :: Pat -> WithEnv Pat
renamePat (i :< PatHole) = return $ i :< PatHole
renamePat (i :< PatVar s) = do
  t <- PatVar <$> lookupNameEnv' s
  return (i :< t)
renamePat (i :< PatApp s []) = return (i :< PatApp s [])
renamePat (i :< PatApp s vs) = do
  vs' <- mapM renamePat vs
  return (i :< PatApp s vs')
