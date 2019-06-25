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
interpret (meta :< TreeAtom "universe") = do
  hole <- newNameWith "univ"
  return $ meta :< WeakTermUniv (UnivLevelHole hole)
interpret (meta :< TreeNode [_ :< TreeAtom "upsilon", _ :< TreeAtom x]) =
  return $ meta :< WeakTermUpsilon x
interpret (meta :< TreeNode [_ :< TreeAtom "epsilon-intro", l]) = do
  l' <- interpretLiteral l
  return $ meta :< WeakTermEpsilonIntro l'
interpret (meta :< TreeNode [_ :< TreeAtom "epsilon-elim", u, e, _ :< TreeNode caseList]) = do
  u' <- interpretIdentifierPlus u
  e' <- interpret e
  caseList' <- mapM interpretClause caseList
  return $ meta :< WeakTermEpsilonElim u' e' caseList'
interpret (meta :< TreeNode [_ :< TreeAtom "pi", s, _ :< TreeNode tus, t]) = do
  s' <- interpretSortal s
  tus' <- mapM interpretIdentifierPlus tus
  t' <- interpret t
  hole <- newNameWith "hole"
  return $ meta :< WeakTermPi s' (tus' ++ [(t', hole)])
interpret (meta :< TreeNode [_ :< TreeAtom "pi-intro", s, _ :< TreeNode tus, e]) = do
  s' <- interpretSortal s
  tus' <- mapM interpretIdentifierPlus tus
  e' <- interpret e
  return $ meta :< WeakTermPiIntro s' tus' e'
interpret (meta :< TreeNode ((_ :< TreeAtom "pi-elim"):s:e:es)) = do
  s' <- interpretSortal s
  e' <- interpret e
  es' <- mapM interpret es
  return $ meta :< WeakTermPiElim s' e' es'
interpret (meta :< TreeNode [_ :< TreeAtom "sigma", s, _ :< TreeNode tus, t]) = do
  s' <- interpretSortal s
  tus' <- mapM interpretIdentifierPlus tus
  t' <- interpret t
  hole <- newNameWith "hole"
  return $ meta :< WeakTermSigma s' (tus' ++ [(t', hole)])
interpret (meta :< TreeNode ((_ :< TreeAtom "sigma-intro"):s:es)) = do
  s' <- interpretSortal s
  es' <- mapM interpret es
  return $ meta :< WeakTermSigmaIntro s' es'
interpret (meta :< TreeNode [_ :< TreeAtom "sigma-elim", s, _ :< TreeNode tus, e1, e2]) = do
  s' <- interpretSortal s
  tus' <- mapM interpretIdentifierPlus tus
  e1' <- interpret e1
  e2' <- interpret e2
  return $ meta :< WeakTermSigmaElim s' tus' e1' e2'
interpret (meta :< TreeNode [_ :< TreeAtom "recurse", ut, e]) = do
  ut' <- interpretIdentifierPlus ut
  e' <- interpret e
  return $ meta :< WeakTermRec ut' e'
interpret (meta :< TreeAtom "_") = do
  name <- newNameWith "hole"
  return $ meta :< WeakTermHole name
--
-- auxiliary interpretations
--
interpret (meta :< TreeNode ((_ :< TreeAtom "arrow"):s:ts)) = do
  s' <- interpretSortal s
  ts' <- mapM interpret ts
  us <- mapM (const $ newNameWith "hole") ts'
  return $ meta :< WeakTermPi s' (zip ts' us)
interpret (meta :< TreeNode ((_ :< TreeAtom "product"):s:ts)) = do
  s' <- interpretSortal s
  ts' <- mapM interpret ts
  us <- mapM (const $ newNameWith "hole") ts'
  return $ meta :< WeakTermSigma s' (zip ts' us)
interpret (meta :< TreeNode (e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  s <- newHole
  return $ meta :< WeakTermPiElim s e' es'
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
  return (t, x)
interpretIdentifierPlus (_ :< TreeNode [t, _ :< TreeAtom x]) = do
  t' <- interpret t
  return (t', x)
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

interpretSortal :: Tree -> WithEnv WeakSortal
interpretSortal (meta :< TreeAtom "primitive") =
  return $ meta :< WeakTermConst "primitive"
interpretSortal s = interpret s

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
