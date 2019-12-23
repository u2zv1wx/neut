module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , extractIdentifier
  ) where

import Control.Monad.Except
import Control.Monad.State
import Text.Read (readMaybe)
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm

interpret :: TreePlus -> WithEnv WeakTermPlus
--
-- foundational interpretations
--
interpret (m, TreeAtom "tau") = withMeta m WeakTermTau
interpret (m, TreeNode [(_, TreeAtom "theta"), (_, TreeAtom x)]) =
  withMeta m $ WeakTermTheta x
interpret (m, TreeNode [(_, TreeAtom "upsilon"), (_, TreeAtom x)]) =
  withMeta m $ WeakTermUpsilon x
interpret (m, TreeNode [(_, TreeAtom "pi"), (_, TreeNode xts), t]) = do
  (xts', t') <- interpretBinder xts t
  withMeta m $ WeakTermPi xts' t'
interpret (m, TreeNode [(_, TreeAtom "pi-introduction"), (_, TreeNode xts), e]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e' <- interpret e
  withMeta m $ WeakTermPiIntro xts' e'
interpret (m, TreeNode ((_, TreeAtom "pi-elimination"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  withMeta m $ WeakTermPiElim e' es'
interpret (m, TreeNode [(_, TreeAtom "mu"), xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  withMeta m $ WeakTermMu xt' e'
interpret (m, TreeNode [(_, TreeAtom "zeta"), (_, TreeAtom x)]) = do
  x' <- interpretAtom x
  withMeta m $ WeakTermZeta x'
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntS i) <- asLowTypeMaybe t
  , i > 0
  , Just x' <- readMaybe x = withMeta m $ WeakTermIntS i x'
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntU i) <- asLowTypeMaybe t
  , i > 0
  , Just x' <- readMaybe x = withMeta m $ WeakTermIntU i x'
interpret (m, TreeNode [(_, TreeAtom "f16"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = do withMeta m $ WeakTermFloat16 x'
interpret (m, TreeNode [(_, TreeAtom "f32"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = do withMeta m $ WeakTermFloat32 x'
interpret (m, TreeNode [(_, TreeAtom "f64"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = do withMeta m $ WeakTermFloat64 x'
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)])
  | Just i <- readNatEnumType x =
    withMeta m $ WeakTermEnum $ EnumTypeNatNum $ fromInteger i
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)]) = do
  isEnum <- isDefinedEnumName x
  if not isEnum
    then throwError $ "No such enum-type defined: " ++ x
    else withMeta m $ WeakTermEnum $ EnumTypeLabel x
interpret (m, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  l' <- interpretEnumValue l
  withMeta m $ WeakTermEnumIntro l'
interpret (m, TreeNode [(_, TreeAtom "enum-elimination"), e, (_, TreeNode cs)]) = do
  e' <- interpret e
  cs' <- mapM interpretClause cs
  withMeta m $ WeakTermEnumElim e' cs'
interpret (m, TreeNode [(_, TreeAtom str), from, to])
  | Just kind <- withKindPrefix str "array" = do
    from' <- interpret from
    to' <- interpret to
    withMeta m $ WeakTermArray kind from' to'
interpret (m, TreeNode [(_, TreeAtom str), (_, TreeNode cs)])
  | Just kind <- withKindPrefix str "array-introduction" = do
    cs' <- mapM interpretClause cs
    let (ls, es) = unzip cs'
    ls' <- mapM asArrayIntro ls
    withMeta m $ WeakTermArrayIntro kind (zip ls' es)
interpret (m, TreeNode [(_, TreeAtom str), e1, e2])
  | Just kind <- withKindPrefix str "array-elimination" = do
    e1' <- interpret e1
    e2' <- interpret e2
    withMeta m $ WeakTermArrayElim kind e1' e2'
--
-- auxiliary interpretations
--
interpret (m, TreeAtom x)
  | Just x' <- readMaybe x = withMeta m $ WeakTermInt x'
interpret (m, TreeAtom x)
  | Just x' <- readMaybe x = withMeta m $ WeakTermFloat x'
interpret (m, TreeAtom x)
  | Just i <- readNatEnumType x =
    withMeta m $ WeakTermEnum $ EnumTypeNatNum $ fromInteger i
interpret (m, TreeAtom x)
  | Just (i, j) <- readNatEnumValue x =
    withMeta m $ WeakTermEnumIntro $ EnumValueNatNum i j
interpret t@(m, TreeAtom x) = do
  ml <- interpretEnumValueMaybe t
  case ml of
    Just l -> withMeta m $ WeakTermEnumIntro l
    _ -> do
      isEnum <- isDefinedEnumName x
      if isEnum
        then withMeta m $ WeakTermEnum $ EnumTypeLabel x
        else do
          b <- isConstant x
          if b
            then withMeta m $ WeakTermTheta x
            else withMeta m $ WeakTermUpsilon x
interpret t@(m, TreeNode es) =
  if null es
    then throwError $ "interpret: syntax error:\n" ++ Pr.ppShow t
    else interpret (m, TreeNode ((m, TreeAtom "pi-elimination") : es))

isConstant :: Identifier -> WithEnv Bool
isConstant x = do
  cenv <- gets constantEnv
  return $ isEnumNatNumConstant x || x `elem` cenv

interpretIdentifierPlus :: TreePlus -> WithEnv IdentifierPlus
interpretIdentifierPlus (_, TreeAtom x) = do
  u <- wrap WeakTermTau
  t <- newHoleOfType u
  return (x, t)
interpretIdentifierPlus (_, TreeNode [(_, TreeAtom x), t]) = do
  x' <- interpretAtom x
  t' <- interpret t
  return (x', t')
interpretIdentifierPlus ut =
  throwError $ "interpretIdentifierPlus: syntax error:\n" ++ Pr.ppShow ut

interpretAtom :: String -> WithEnv String
interpretAtom "_" = newNameWith "hole"
interpretAtom x = return x

interpretEnumValueMaybe :: TreePlus -> WithEnv (Maybe EnumValue)
interpretEnumValueMaybe (_, TreeAtom x)
  | Just (i, j) <- readNatEnumValue x = return $ Just $ EnumValueNatNum i j
interpretEnumValueMaybe (_, TreeAtom x) = do
  b <- isDefinedEnum x
  if b
    then return $ Just $ EnumValueLabel x
    else throwError $ "no such label defined: " ++ x
interpretEnumValueMaybe _ = return Nothing

interpretEnumValue :: TreePlus -> WithEnv EnumValue
interpretEnumValue l = do
  ml' <- interpretEnumValueMaybe l
  case ml' of
    Just l' -> return l'
    Nothing -> throwError $ "interpretEnumValue: syntax error:\n" ++ Pr.ppShow l

interpretBinder ::
     [TreePlus] -> TreePlus -> WithEnv ([IdentifierPlus], WeakTermPlus)
interpretBinder xts t = do
  xts' <- mapM interpretIdentifierPlus xts
  t' <- interpret t
  return (xts', t')

interpretCase :: TreePlus -> WithEnv Case
--
-- foundational
--
interpretCase (_, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  CaseValue <$> interpretEnumValue l
interpretCase (_, TreeAtom "default") = return CaseDefault
--
-- auxiliary
--
interpretCase c = do
  l <- interpretEnumValue c
  return $ CaseValue l

interpretClause :: TreePlus -> WithEnv (Case, WeakTermPlus)
interpretClause (_, TreeNode [c, e]) = do
  c' <- interpretCase c
  e' <- interpret e
  return (c', e')
interpretClause e =
  throwError $ "interpretClause: syntax error:\n " ++ Pr.ppShow e

asArrayIntro :: Case -> WithEnv EnumValue
asArrayIntro (CaseValue l) = return l
asArrayIntro CaseDefault = throwError "`default` cannot be used in array-intro"

withMeta :: TreeMeta -> WeakTerm -> WithEnv WeakTermPlus
withMeta m e = do
  m' <- toWeakMeta m
  return (m', e)

extractIdentifier :: TreePlus -> WithEnv Identifier
extractIdentifier (_, TreeAtom s) = return s
extractIdentifier t =
  throwError $ "interpretAtom: syntax error:\n" ++ Pr.ppShow t

withKindPrefix :: String -> String -> Maybe ArrayKind
withKindPrefix str base
  | [t, base'] <- wordsBy '-' str -- e.g. u8-array
  , base == base'
  , Just t' <- asLowTypeMaybe t
  , Just kind <- asArrayKind t' = Just kind
withKindPrefix _ _ = Nothing
