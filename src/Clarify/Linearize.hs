module Clarify.Linearize
  ( linearize,
  )
where

import Clarify.Utility
import Control.Monad.State
import Data.Basic
import Data.Comp
import Data.Env

linearize ::
  [(Ident, CompPlus)] -> -- [(x1, t1), ..., (xn, tn)]  (closed chain)
  CompPlus -> -- a term that can contain non-linear occurrences of xi
  WithEnv CompPlus -- a term in which all the variables in the closed chain occur linearly
linearize binder e =
  case binder of
    [] ->
      return e
    (x, t) : xts -> do
      e' <- linearize xts e
      (newNameList, e'') <- distinguishComp x e'
      case newNameList of
        [] ->
          insertFooter x t e''
        z : zs ->
          insertHeader x z zs t e''

insertFooter :: Ident -> CompPlus -> CompPlus -> WithEnv CompPlus
insertFooter x t e@(m, _) = do
  ans <- newIdentFromText "answer"
  hole <- newIdentFromText "unit"
  discardUnusedVar <- toAffineApp m x t
  return (m, CompUpElim ans e (m, CompUpElim hole discardUnusedVar (m, CompUpIntro (m, ValueVar ans))))

insertHeader ::
  Ident ->
  Ident ->
  [Ident] ->
  CompPlus ->
  CompPlus ->
  WithEnv CompPlus
insertHeader x z1 zs t e@(m, _) = do
  case zs of
    [] ->
      return (m, CompUpElim z1 (m, CompUpIntro (m, ValueVar x)) e)
    z2 : rest -> do
      e' <- insertHeader x z2 rest t e
      copyRelevantVar <- toRelevantApp m x t
      return (m, CompUpElim z1 copyRelevantVar e')

distinguishValue :: Ident -> ValuePlus -> WithEnv ([Ident], ValuePlus)
distinguishValue z term =
  case term of
    (m, ValueVar x) ->
      if x /= z
        then return ([], term)
        else do
          x' <- newIdentFromIdent x
          return ([x'], (m, ValueVar x'))
    (m, ValueSigmaIntro ds) -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat vss, (m, ValueSigmaIntro ds'))
    _ ->
      return ([], term)

distinguishComp :: Ident -> CompPlus -> WithEnv ([Ident], CompPlus)
distinguishComp z term =
  case term of
    (m, CompPrimitive theta) -> do
      (vs, theta') <- distinguishPrimitive z theta
      return (vs, (m, CompPrimitive theta'))
    (m, CompPiElimDownElim d ds) -> do
      (vs, d') <- distinguishValue z d
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat $ vs : vss, (m, CompPiElimDownElim d' ds'))
    (m, CompSigmaElim b xs d e) -> do
      (vs1, d') <- distinguishValue z d
      (vs2, e') <- distinguishComp z e
      return (concat [vs1, vs2], (m, CompSigmaElim b xs d' e'))
    (m, CompUpIntro d) -> do
      (vs, d') <- distinguishValue z d
      return (vs, (m, CompUpIntro d'))
    (m, CompUpElim x e1 e2) -> do
      (vs1, e1') <- distinguishComp z e1
      (vs2, e2') <- distinguishComp z e2
      return (concat [vs1, vs2], (m, CompUpElim x e1' e2'))
    (m, CompEnumElim d branchList) -> do
      (vs, d') <- distinguishValue z d
      case branchList of
        [] ->
          return (vs, (m, CompEnumElim d' []))
        _ -> do
          let (cs, es) = unzip branchList
          envBefore <- get
          (vsses, envAfterList) <- fmap unzip $ forM es $ \e -> liftIO $ runStateT (distinguishComp z e) envBefore
          let (vss, es') = unzip vsses
          put (head envAfterList)
          return (concat $ [vs, head vss], (m, CompEnumElim d' (zip cs es')))

distinguishPrimitive :: Ident -> Primitive -> WithEnv ([Ident], Primitive)
distinguishPrimitive z term =
  case term of
    PrimitivePrimOp op ds -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat vss, PrimitivePrimOp op ds')
    PrimitiveDerangement k ds -> do
      (vss, ds') <- unzip <$> mapM (distinguishValue z) ds
      return (concat vss, PrimitiveDerangement k ds')
