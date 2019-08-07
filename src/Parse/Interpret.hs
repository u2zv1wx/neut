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
interpret (m :< TreeNode [_ :< TreeAtom "pi", _ :< TreeAtom i, _ :< TreeNode xts, t]) = do
  i' <- interpretWeakLevel i
  binder <- interpretBinder xts t
  return $ m :< WeakTermPi i' binder
interpret (m :< TreeNode [_ :< TreeAtom "pi-intro", _ :< TreeAtom i, _ :< TreeNode xts, e]) = do
  i' <- interpretWeakLevel i
  xts' <- mapM interpretIdentifierPlus xts
  e' <- interpret e
  return $ m :< WeakTermPiIntro i' xts' e'
interpret (m :< TreeNode ((_ :< TreeAtom "pi-elim"):(_ :< TreeAtom i):e:es)) = do
  i' <- interpretWeakLevel i
  e' <- interpret e
  es' <- mapM interpret es
  return $ m :< WeakTermPiElim i' e' es'
interpret (m :< TreeNode [_ :< TreeAtom "sigma", _ :< TreeAtom i, _ :< TreeNode xts, t]) = do
  i' <- interpretWeakLevel i
  binder <- interpretBinder xts t
  return $ m :< WeakTermSigma i' binder
interpret (m :< TreeNode ((_ :< TreeAtom "sigma-intro"):(_ :< TreeAtom i):es)) = do
  i' <- interpretWeakLevel i
  es' <- mapM interpret es
  return $ m :< WeakTermSigmaIntro i' es'
interpret (m :< TreeNode [_ :< TreeAtom "sigma-elim", _ :< TreeAtom i, _ :< TreeNode xts, e1, e2]) = do
  i' <- interpretWeakLevel i
  xts' <- mapM interpretIdentifierPlus xts
  e1' <- interpret e1
  e2' <- interpret e2
  return $ m :< WeakTermSigmaElim i' xts' e1' e2'
interpret (m :< TreeNode [_ :< TreeAtom "tau", _ :< TreeAtom i, t]) = do
  i' <- interpretWeakLevel i
  t' <- interpret t
  return $ m :< WeakTermTau i' t'
interpret (m :< TreeNode [_ :< TreeAtom "tau-intro", _ :< TreeAtom i, e]) = do
  i' <- interpretWeakLevel i
  e' <- interpret e
  return $ m :< WeakTermTauIntro i' e'
interpret (m :< TreeNode [_ :< TreeAtom "tau-elim", _ :< TreeAtom i, e]) = do
  i' <- interpretWeakLevel i
  e' <- interpret e
  return $ m :< WeakTermTauElim i' e'
interpret (m :< TreeNode [_ :< TreeAtom "theta", t]) = do
  t' <- interpret t
  return $ m :< WeakTermTheta t'
interpret (m :< TreeNode [_ :< TreeAtom "theta-intro", e]) = do
  e' <- interpret e
  return $ m :< WeakTermThetaIntro e'
interpret (m :< TreeNode [_ :< TreeAtom "theta-elim", e, _ :< TreeAtom i]) = do
  e' <- interpret e
  i' <- interpretWeakLevel i
  return $ m :< WeakTermThetaElim e' i'
interpret (m :< TreeNode [_ :< TreeAtom "mu", xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  return $ m :< WeakTermMu xt' e'
interpret (m :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ m :< WeakTermHole (name, WeakLevelInt 0)
--
-- auxiliary interpretations
--
interpret (m :< TreeAtom "universe") = do
  name <- newNameWith "univ"
  return $ m :< WeakTermUniv (WeakLevelHole (name, WeakLevelInt 0))
interpret (m :< TreeNode ((_ :< TreeAtom "arrow"):(_ :< TreeAtom i):ts)) = do
  i' <- interpretWeakLevel i
  ts' <- mapM interpret ts
  xs <- mapM (const $ newNameWith "hole") ts'
  return $ m :< WeakTermPi i' (zip xs ts')
interpret (m :< TreeNode ((_ :< TreeAtom "product"):(_ :< TreeAtom i):ts)) = do
  i' <- interpretWeakLevel i
  ts' <- mapM interpret ts
  xs <- mapM (const $ newNameWith "hole") ts'
  return $ m :< WeakTermSigma i' (zip xs ts')
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
  return $ WeakLevelHole (h, WeakLevelInt 0)
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
