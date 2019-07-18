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
interpret (meta :< TreeNode [_ :< TreeAtom "universe", _ :< TreeAtom x]) = do
  l <- interpretWeakLevel x
  return $ meta :< WeakTermUniv l
interpret (meta :< TreeNode [_ :< TreeAtom "upsilon", _ :< TreeAtom x]) =
  return $ meta :< WeakTermUpsilon x
interpret (meta :< TreeNode [_ :< TreeAtom "epsilon-intro", l]) = do
  l' <- interpretLiteral l
  return $ meta :< WeakTermEpsilonIntro l'
interpret (meta :< TreeNode [_ :< TreeAtom "epsilon-elim", xt, e, _ :< TreeNode caseList]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  caseList' <- mapM interpretClause caseList
  return $ meta :< WeakTermEpsilonElim xt' e' caseList'
interpret (meta :< TreeNode [_ :< TreeAtom "pi", _ :< TreeNode xts, t]) = do
  binder <- interpretBinder xts t
  return $ meta :< WeakTermPi binder
interpret (meta :< TreeNode [_ :< TreeAtom "pi-intro", _ :< TreeNode xts, e]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e' <- interpret e
  return $ meta :< WeakTermPiIntro xts' e'
interpret (meta :< TreeNode ((_ :< TreeAtom "pi-elim"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  return $ meta :< WeakTermPiElim e' es'
interpret (meta :< TreeNode [_ :< TreeAtom "sigma", _ :< TreeNode xts, t]) = do
  binder <- interpretBinder xts t
  return $ meta :< WeakTermPi binder
interpret (meta :< TreeNode ((_ :< TreeAtom "sigma-intro"):es)) = do
  es' <- mapM interpret es
  return $ meta :< WeakTermSigmaIntro es'
interpret (meta :< TreeNode [_ :< TreeAtom "sigma-elim", _ :< TreeNode xts, e1, e2]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e1' <- interpret e1
  e2' <- interpret e2
  return $ meta :< WeakTermSigmaElim xts' e1' e2'
interpret (meta :< TreeNode [_ :< TreeAtom "tau", t]) = do
  t' <- interpret t
  return $ meta :< WeakTermTau t'
interpret (meta :< TreeNode [_ :< TreeAtom "tau-intro", e]) = do
  e' <- interpret e
  return $ meta :< WeakTermTauIntro e'
interpret (meta :< TreeNode [_ :< TreeAtom "tau-elim", e]) = do
  e' <- interpret e
  return $ meta :< WeakTermTauElim e'
interpret (meta :< TreeNode [_ :< TreeAtom "theta", t]) = do
  t' <- interpret t
  return $ meta :< WeakTermTheta t'
interpret (meta :< TreeNode [_ :< TreeAtom "theta-intro", e]) = do
  e' <- interpret e
  return $ meta :< WeakTermThetaIntro e'
interpret (meta :< TreeNode [_ :< TreeAtom "theta-elim", e]) = do
  e' <- interpret e
  return $ meta :< WeakTermThetaElim e'
interpret (meta :< TreeNode [_ :< TreeAtom "mu", xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  return $ meta :< WeakTermMu xt' e'
interpret (meta :< TreeNode [_ :< TreeAtom "iota", e, _ :< TreeAtom x]) = do
  l <- interpretWeakLevel x
  e' <- interpret e
  return $ meta :< WeakTermIota e' l
interpret (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ meta :< WeakTermHole name
--
-- auxiliary interpretations
--
interpret (meta :< TreeAtom "universe") = do
  hole <- newNameWith "univ"
  return $ meta :< WeakTermUniv (WeakLevelHole hole)
interpret (meta :< TreeNode ((_ :< TreeAtom "arrow"):ts)) = do
  ts' <- mapM interpret ts
  xs <- mapM (const $ newNameWith "hole") ts'
  return $ meta :< WeakTermPi (zip xs ts')
interpret (meta :< TreeNode ((_ :< TreeAtom "product"):ts)) = do
  ts' <- mapM interpret ts
  xs <- mapM (const $ newNameWith "hole") ts'
  return $ meta :< WeakTermSigma (zip xs ts')
interpret (meta :< TreeNode (e:es)) =
  interpret $ meta :< TreeNode (("" :< TreeAtom "pi-elim") : e : es)
interpret t@(meta :< TreeAtom x) = do
  ml <- interpretLiteralMaybe t
  case ml of
    Just l -> return $ meta :< WeakTermEpsilonIntro l
    Nothing -> do
      isSortal <- isDefinedIndexName x
      if isSortal
        then return $ meta :< WeakTermEpsilon x
        else do
          cenv <- gets constantEnv
          if x `elem` cenv
            then return $ meta :< WeakTermConst x
            else return $ meta :< WeakTermUpsilon x
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
