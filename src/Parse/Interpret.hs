module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , extractIdentifier
  ) where

import           Control.Comonad.Cofree
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
interpret (m :< TreeNode [_ :< TreeAtom "universe", _ :< TreeAtom x]) = do
  l <- interpretWeakLevel x
  return $ m :< WeakTermUniv l
interpret (m :< TreeNode [_ :< TreeAtom "upsilon", _ :< TreeAtom x]) =
  return $ m :< WeakTermUpsilon x
interpret (m :< TreeNode [_ :< TreeAtom "epsilon-intro", l]) = do
  l' <- interpretLiteral l
  return $ m :< WeakTermEpsilonIntro l'
interpret (m :< TreeNode [_ :< TreeAtom "epsilon-elim", xt, e, _ :< TreeNode caseList]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  caseList' <- mapM interpretClause caseList
  return $ m :< WeakTermEpsilonElim xt' e' caseList'
interpret (m :< TreeNode [_ :< TreeAtom "pi", _ :< TreeNode xts, t]) = do
  binder <- interpretBinder xts t
  return $ m :< WeakTermPi binder
interpret (m :< TreeNode [_ :< TreeAtom "pi-intro", _ :< TreeNode xts, e]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e' <- interpret e
  return $ m :< WeakTermPiIntro xts' e'
interpret (m :< TreeNode ((_ :< TreeAtom "pi-elim"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  return $ m :< WeakTermPiElim e' es'
interpret (m :< TreeNode [_ :< TreeAtom "sigma", _ :< TreeNode xts, t]) = do
  binder <- interpretBinder xts t
  return $ m :< WeakTermPi binder
interpret (m :< TreeNode ((_ :< TreeAtom "sigma-intro"):es)) = do
  es' <- mapM interpret es
  return $ m :< WeakTermSigmaIntro es'
interpret (m :< TreeNode [_ :< TreeAtom "sigma-elim", _ :< TreeNode xts, e1, e2]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e1' <- interpret e1
  e2' <- interpret e2
  return $ m :< WeakTermSigmaElim xts' e1' e2'
interpret (m :< TreeNode [_ :< TreeAtom "tau", t]) = do
  t' <- interpret t
  return $ m :< WeakTermTau t'
interpret (m :< TreeNode [_ :< TreeAtom "tau-intro", e]) = do
  e' <- interpret e
  return $ m :< WeakTermTauIntro e'
interpret (m :< TreeNode [_ :< TreeAtom "tau-elim", e]) = do
  e' <- interpret e
  return $ m :< WeakTermTauElim e'
interpret (m :< TreeNode [_ :< TreeAtom "theta", t]) = do
  t' <- interpret t
  return $ m :< WeakTermTheta t'
interpret (m :< TreeNode [_ :< TreeAtom "theta-intro", e]) = do
  e' <- interpret e
  return $ m :< WeakTermThetaIntro e'
interpret (m :< TreeNode [_ :< TreeAtom "theta-elim", e]) = do
  e' <- interpret e
  return $ m :< WeakTermThetaElim e'
interpret (m :< TreeNode [_ :< TreeAtom "mu", xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  return $ m :< WeakTermMu xt' e'
interpret (m :< TreeNode [_ :< TreeAtom "iota", e, _ :< TreeAtom x]) = do
  l <- interpretWeakLevel x
  e' <- interpret e
  return $ m :< WeakTermIota e' l
interpret (m :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ m :< WeakTermHole name
--
-- auxiliary interpretations
--
interpret (m :< TreeAtom "universe") = do
  hole <- newNameWith "univ"
  return $ m :< WeakTermUniv (WeakLevelHole hole)
interpret (m :< TreeNode ((_ :< TreeAtom "arrow"):ts)) = do
  ts' <- mapM interpret ts
  xs <- mapM (const $ newNameWith "hole") ts'
  return $ m :< WeakTermPi (zip xs ts')
interpret (m :< TreeNode ((_ :< TreeAtom "product"):ts)) = do
  ts' <- mapM interpret ts
  xs <- mapM (const $ newNameWith "hole") ts'
  return $ m :< WeakTermSigma (zip xs ts')
interpret (m :< TreeNode (e:es)) =
  interpret $ m :< TreeNode (("" :< TreeAtom "pi-elim") : e : es)
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
interpret t = lift $ throwE $ "interpret: syntax error:\n" ++ Pr.ppShow t

interpretIdentifierPlus :: Tree -> WithEnv IdentifierPlus
interpretIdentifierPlus (_ :< TreeAtom x) = do
  t <- newHole
  return (x, t)
interpretIdentifierPlus (_ :< TreeNode [t, _ :< TreeAtom x]) = do
  t' <- interpret t
  return (x, t')
interpretIdentifierPlus ut =
  lift $ throwE $ "interpretIdentifierPlus: syntax error:\n" ++ Pr.ppShow ut

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

interpretWeakLevel :: String -> WithEnv WeakLevel
interpretWeakLevel x
  | Just i <- readMaybe x = return $ WeakLevelInt i
interpretWeakLevel "infinity" = return WeakLevelInfinity
interpretWeakLevel "_" = do
  h <- newNameWith "hole"
  return $ WeakLevelHole h
interpretWeakLevel s =
  lift $ throwE $ "interpretWeakLevel: syntax error:\n" ++ s

interpretCase :: Tree -> WithEnv Case
--
-- foundational
--
interpretCase (_ :< TreeNode [_ :< TreeAtom "epsilon-intro", l]) = do
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
