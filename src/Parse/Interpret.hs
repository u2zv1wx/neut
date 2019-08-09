module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , extractIdentifier
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Text.Read                  (readMaybe)
import qualified Text.Show.Pretty           as Pr

import           Data.Basic
import           Data.Env
import           Data.Tree
import           Data.WeakTerm

interpret :: Tree -> WithEnv WeakTerm
--
-- foundational interpretations
--
interpret (m :< TreeAtom "universe") = return $ m :< WeakTermUniverse
interpret (m :< TreeNode [_ :< TreeAtom "upsilon", _ :< TreeAtom x]) =
  return $ m :< WeakTermUpsilon x
interpret (m :< TreeNode [_ :< TreeAtom "epsilon", _ :< TreeAtom x]) = do
  isSortal <- isDefinedIndexName x
  if isSortal
    then return $ m :< WeakTermEpsilon x
    else throwError $ "No such epsilon-type defined: " ++ x
interpret (m :< TreeNode [_ :< TreeAtom "epsilon-introduction", l]) = do
  l' <- interpretLiteral l
  return $ m :< WeakTermEpsilonIntro l'
interpret (m :< TreeNode [_ :< TreeAtom "epsilon-elimination", xt, e, _ :< TreeNode cs]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  cs' <- mapM interpretClause cs
  return $ m :< WeakTermEpsilonElim xt' e' cs'
interpret (m :< TreeNode [_ :< TreeAtom "pi", _ :< TreeNode xts, t]) = do
  binder <- interpretBinder xts t
  return $ m :< WeakTermPi binder
interpret (m :< TreeNode [_ :< TreeAtom "pi-introduction", _ :< TreeNode xts, e]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e' <- interpret e
  return $ m :< WeakTermPiIntro xts' e'
interpret (m :< TreeNode ((_ :< TreeAtom "pi-elimination"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  return $ m :< WeakTermPiElim e' es'
interpret (m :< TreeNode [_ :< TreeAtom "sigma", _ :< TreeNode xts, t]) = do
  binder <- interpretBinder xts t
  return $ m :< WeakTermSigma binder
interpret (m :< TreeNode ((_ :< TreeAtom "sigma-introduction"):es)) = do
  es' <- mapM interpret es
  return $ m :< WeakTermSigmaIntro es'
interpret (m :< TreeNode [_ :< TreeAtom "sigma-elimination", _ :< TreeNode xts, e1, e2]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e1' <- interpret e1
  e2' <- interpret e2
  return $ m :< WeakTermSigmaElim xts' e1' e2'
interpret (m :< TreeNode [_ :< TreeAtom "mu", xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  return $ m :< WeakTermMu xt' e'
interpret (m :< TreeNode [_ :< TreeAtom "hole", _ :< TreeAtom x]) = do
  x' <- interpretAtom x
  return $ m :< WeakTermHole x'
--
-- auxiliary interpretations
--
interpret t@(m :< TreeAtom x) = do
  ml <- interpretLiteralMaybe t
  case ml of
    Just l -> return $ m :< WeakTermEpsilonIntro l
    Nothing -> do
      isSortal <- isDefinedIndexName x
      if isSortal
        then return $ m :< WeakTermEpsilon x
        else do
          cenv <- gets constantEnv
          if x `elem` cenv
            then return $ m :< WeakTermConst x
            else return $ m :< WeakTermUpsilon x
interpret (m :< TreeNode (e:es)) =
  interpret $ m :< TreeNode (("" :< TreeAtom "pi-elimination") : e : es)
interpret t = lift $ throwE $ "interpret: syntax error:\n" ++ Pr.ppShow t

interpretIdentifierPlus :: Tree -> WithEnv IdentifierPlus
interpretIdentifierPlus (_ :< TreeAtom x) = do
  t <- newHole
  return (x, t)
interpretIdentifierPlus (_ :< TreeNode [_ :< TreeAtom x, t]) = do
  x' <- interpretAtom x
  t' <- interpret t
  return (x', t')
interpretIdentifierPlus ut =
  lift $ throwE $ "interpretIdentifierPlus: syntax error:\n" ++ Pr.ppShow ut

interpretAtom :: String -> WithEnv String
interpretAtom "_" = newNameWith "hole"
interpretAtom x   = return x

interpretLiteralMaybe :: Tree -> WithEnv (Maybe Literal)
interpretLiteralMaybe (_ :< TreeAtom x)
  | Just f <- readMaybe x
  , '.' `elem` x = return $ Just $ LiteralFloat f
interpretLiteralMaybe (_ :< TreeAtom x)
  | Just i <- readMaybe x = return $ Just $ LiteralInteger i
interpretLiteralMaybe (_ :< TreeAtom x) = do
  b <- isDefinedIndex x
  if b
    then return $ Just $ LiteralLabel x
    else lift $ throwE $ "no such label defined: " ++ x
interpretLiteralMaybe _ = return Nothing

interpretLiteral :: Tree -> WithEnv Literal
interpretLiteral l = do
  ml' <- interpretLiteralMaybe l
  case ml' of
    Just l' -> return l'
    Nothing ->
      lift $ throwE $ "interpretLiteral: syntax error:\n" ++ Pr.ppShow l

interpretBinder :: [Tree] -> Tree -> WithEnv [IdentifierPlus]
interpretBinder xts t = do
  xts' <- mapM interpretIdentifierPlus xts
  t' <- interpret t
  hole <- newNameWith "hole"
  return $ xts' ++ [(hole, t')]

interpretCase :: Tree -> WithEnv Case
--
-- foundational
--
interpretCase (_ :< TreeNode [_ :< TreeAtom "epsilon-introduction", l]) = do
  l' <- interpretLiteral l
  return $ CaseLiteral l'
interpretCase (_ :< TreeAtom "default") = return CaseDefault
--
-- auxiliary
--
interpretCase c = do
  mc' <- interpretLiteralMaybe c
  case mc' of
    Just l -> return $ CaseLiteral l
    Nothing -> lift $ throwE $ "interpretCase: syntax error:\n" ++ Pr.ppShow c

interpretClause :: Tree -> WithEnv (Case, WeakTerm)
interpretClause (_ :< TreeNode [c, e]) = do
  c' <- interpretCase c
  e' <- interpret e
  return (c', e')
interpretClause e =
  lift $ throwE $ "interpretClause: syntax error:\n " ++ Pr.ppShow e

extractIdentifier :: Tree -> WithEnv Identifier
extractIdentifier (_ :< TreeAtom s) = return s
extractIdentifier t =
  lift $ throwE $ "interpretAtom: syntax error:\n" ++ Pr.ppShow t
