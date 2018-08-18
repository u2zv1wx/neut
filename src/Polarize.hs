module Polarize where

import           Control.Monad

import           Control.Comonad.Cofree

import           Control.Monad.State
import           Control.Monad.Trans.Except

import qualified Text.Show.Pretty           as Pr

import           Data
import           Pattern

polarizeType :: WeakType -> WithEnv Type
polarizeType (WeakTypeVar i) = return $ TypeValueType (ValueTypeVar i)
polarizeType (WeakTypePosHole i) = return $ TypeValueType (ValueTypeVar i)
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

polarizeTypeEnv :: [(Identifier, WeakType)] -> WithEnv ()
polarizeTypeEnv [] = return ()
polarizeTypeEnv ((i, wt):ts) = do
  wt' <- polarizeType wt
  case wt' of
    TypeCompType ct  -> insCTEnv i ct
    TypeValueType vt -> insVTEnv i vt
  polarizeTypeEnv ts
