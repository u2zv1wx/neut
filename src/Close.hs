module Close
  ( close
  ) where

import Control.Monad

import Control.Comonad.Cofree

import Control.Monad.State
import Control.Monad.Trans.Except

import qualified Text.Show.Pretty as Pr

import Data
import Reduce
import Util

import Text.Read (readMaybe)

import Data.Maybe (isJust, maybeToList)

-- this function translates `mu x. e` into:
--   (mu x. lam env. let (y1, ..., yn) := env in e {x := x @ env}) @ (y1, ..., ym)
-- where (y1, ..., ym) is the free variables of e. In other words, this function
-- "closes" mu-operator with respect to its free variables.
close :: Term -> WithEnv Term
close (TermVar x) = return $ TermVar x
close (TermConst x) = return $ TermConst x
close (TermPiIntro x e) = do
  e' <- close e
  return $ TermPiIntro x e'
close (TermPiElim e1 e2) = do
  e1' <- close e1
  e2' <- close e2
  return $ TermPiElim e1' e2'
close (TermSigmaIntro es) = do
  es' <- mapM close es
  return $ TermSigmaIntro es'
close (TermSigmaElim e1 xs e2) = do
  e1' <- close e1
  e2' <- close e2
  return $ TermSigmaElim e1' xs e2'
close (TermIndexIntro l meta) = return $ TermIndexIntro l meta
close (TermIndexElim e branchList) = do
  let (labelList, es) = unzip branchList
  e' <- close e
  es' <- mapM close es
  return $ TermIndexElim e' $ zip labelList es'
close (TermMu x e) = do
  let fvs = varTerm (TermMu x e)
  env <- newNameWith "env"
  return $
    TermPiElim
      (TermMu x $
       TermPiIntro
         env
         (TermSigmaElim
            (TermVar env)
            fvs
            (substTerm [(x, TermPiElim (TermConst x) (TermVar env))] e)))
      (TermSigmaIntro $ map TermVar fvs)

varTerm :: Term -> [Identifier]
varTerm (TermVar x) = [x]
varTerm (TermConst _) = []
varTerm (TermPiIntro x e) = filter (/= x) $ varTerm e
varTerm (TermPiElim e1 e2) = varTerm e1 ++ varTerm e2
varTerm (TermSigmaIntro es) = concatMap varTerm es
varTerm (TermSigmaElim e1 xs e2) =
  varTerm e1 ++ filter (`notElem` xs) (varTerm e2)
varTerm (TermIndexIntro _ _) = []
varTerm (TermIndexElim e branchList) = do
  let (_, es) = unzip branchList
  varTerm e ++ concatMap varTerm es
varTerm (TermMu x e) = filter (/= x) $ varTerm e
