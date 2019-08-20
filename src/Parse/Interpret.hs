module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , extractIdentifier
  ) where

import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Text.Read                  (readMaybe)
import qualified Text.Show.Pretty           as Pr

import           Data.Basic
import           Data.Env
import           Data.Tree
import           Data.WeakTerm

interpret :: TreePlus -> WithEnv WeakTermPlus
--
-- foundational interpretations
--
interpret (m, TreeAtom "tau") = withMeta m WeakTermTau
interpret (m, TreeNode [(_, TreeAtom "theta"), (_, TreeAtom x)]) =
  withMeta m $ WeakTermTheta x
interpret (m, TreeNode [(_, TreeAtom "upsilon"), (_, TreeAtom x)]) =
  withMeta m $ WeakTermUpsilon x
interpret (m, TreeNode [(_, TreeAtom "epsilon"), (_, TreeAtom x)]) = do
  isEpsilon <- isDefinedEpsilonName x
  if not isEpsilon
    then throwError $ "No such epsilon-type defined: " ++ x
    else withMeta m $ WeakTermEpsilon x
interpret (m, TreeNode [(_, TreeAtom "epsilon-introduction"), l]) = do
  l' <- interpretLiteral l
  withMeta m $ WeakTermEpsilonIntro l'
interpret (m, TreeNode [(_, TreeAtom "epsilon-elimination"), xt, e, (_, TreeNode cs)]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  cs' <- mapM interpretClause cs
  withMeta m $ WeakTermEpsilonElim xt' e' cs'
interpret (m, TreeNode [(_, TreeAtom "pi"), (_, TreeNode xts), t]) = do
  (xts', t') <- interpretBinder xts t
  h <- newNameWith "hole"
  withMeta m $ WeakTermPi $ xts' ++ [(h, t')]
interpret (m, TreeNode [(_, TreeAtom "pi-introduction"), (_, TreeNode xts), e]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e' <- interpret e
  withMeta m $ WeakTermPiIntro xts' e'
interpret (m, TreeNode ((_, TreeAtom "pi-elimination"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  withMeta m $ WeakTermPiElim e' es'
interpret (m, TreeNode [(_, TreeAtom "sigma"), (_, TreeNode xts), t]) = do
  (xts', t') <- interpretBinder xts t
  h <- newNameWith "hole"
  withMeta m $ WeakTermSigma $ xts' ++ [(h, t')]
interpret (m, TreeNode ((_, TreeAtom "sigma-introduction"):es)) = do
  es' <- mapM interpret es
  withMeta m $ WeakTermSigmaIntro es'
interpret (m, TreeNode [(_, TreeAtom "sigma-elimination"), (_, TreeNode xts), e1, e2]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e1' <- interpret e1
  e2' <- interpret e2
  withMeta m $ WeakTermSigmaElim xts' e1' e2'
interpret (m, TreeNode [(_, TreeAtom "mu"), xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  withMeta m $ WeakTermMu xt' e'
interpret (m, TreeNode [(_, TreeAtom "zeta"), (_, TreeAtom x)]) = do
  x' <- interpretAtom x
  withMeta m $ WeakTermZeta x'
--
-- auxiliary interpretations
--
interpret t@(m, TreeAtom x) = do
  ml <- interpretLiteralMaybe t
  case ml of
    Just l -> withMeta m $ WeakTermEpsilonIntro l
    Nothing -> do
      isEpsilon <- isDefinedEpsilonName x
      if isEpsilon
        then withMeta m $ WeakTermEpsilon x
        else do
          cenv <- gets constantEnv
          if x `elem` cenv
            then withMeta m $ WeakTermTheta x
            else withMeta m $ WeakTermUpsilon x
interpret t@(m, TreeNode es) =
  if null es
    then throwError $ "interpret: syntax error:\n" ++ Pr.ppShow t
    else interpret (m, TreeNode ((m, TreeAtom "pi-elimination") : es))

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
  lift $ throwE $ "interpretIdentifierPlus: syntax error:\n" ++ Pr.ppShow ut

interpretAtom :: String -> WithEnv String
interpretAtom "_" = newNameWith "hole"
interpretAtom x   = return x

interpretLiteralMaybe :: TreePlus -> WithEnv (Maybe Literal)
interpretLiteralMaybe (_, TreeAtom x)
  | Just f <- readMaybe x
  , '.' `elem` x = return $ Just $ LiteralFloat f
interpretLiteralMaybe (_, TreeAtom x)
  | Just i <- readMaybe x = return $ Just $ LiteralInteger i
interpretLiteralMaybe (_, TreeAtom x) = do
  b <- isDefinedEpsilon x
  if b
    then return $ Just $ LiteralLabel x
    else lift $ throwE $ "no such label defined: " ++ x
interpretLiteralMaybe _ = return Nothing

interpretLiteral :: TreePlus -> WithEnv Literal
interpretLiteral l = do
  ml' <- interpretLiteralMaybe l
  case ml' of
    Just l' -> return l'
    Nothing ->
      lift $ throwE $ "interpretLiteral: syntax error:\n" ++ Pr.ppShow l

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
interpretCase (_, TreeNode [(_, TreeAtom "epsilon-introduction"), l]) = do
  l' <- interpretLiteral l
  return $ CaseLiteral l'
interpretCase (_, TreeAtom "default") = return CaseDefault
--
-- auxiliary
--
interpretCase c = do
  mc' <- interpretLiteralMaybe c
  case mc' of
    Just l -> return $ CaseLiteral l
    Nothing -> lift $ throwE $ "interpretCase: syntax error:\n" ++ Pr.ppShow c

interpretClause :: TreePlus -> WithEnv (Case, WeakTermPlus)
interpretClause (_, TreeNode [c, e]) = do
  c' <- interpretCase c
  e' <- interpret e
  return (c', e')
interpretClause e =
  lift $ throwE $ "interpretClause: syntax error:\n " ++ Pr.ppShow e

withMeta :: TreeMeta -> WeakTerm -> WithEnv WeakTermPlus
withMeta m e = do
  m' <- toWeakMeta m
  return (m', e)

extractIdentifier :: TreePlus -> WithEnv Identifier
extractIdentifier (_, TreeAtom s) = return s
extractIdentifier t =
  lift $ throwE $ "interpretAtom: syntax error:\n" ++ Pr.ppShow t
