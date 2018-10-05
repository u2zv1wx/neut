module Reduce where

import           Data

import           Control.Comonad

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.Identity
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Text.Show.Deriving

import           Data.Functor.Classes

import           System.IO.Unsafe

import           Data.IORef
import           Data.List
import           Data.Maybe                 (fromMaybe)
import           Data.Tuple                 (swap)

import qualified Text.Show.Pretty           as Pr

reduce :: Neut -> WithEnv Neut
reduce (i :< NeutPiElim e1 e2) = do
  e2' <- reduce e2
  e1' <- reduce e1
  case e1' of
    _ :< NeutPiIntro (arg, _) body -> do
      let sub = [(arg, e2')]
      let _ :< body' = subst sub body
      reduce $ i :< body'
    _ -> return $ i :< NeutPiElim e1' e2'
reduce (i :< NeutSigmaIntro es) = do
  es' <- mapM reduce es
  return $ i :< NeutSigmaIntro es'
reduce (i :< NeutSigmaElim e xs body) = do
  e' <- reduce e
  case e of
    _ :< NeutSigmaIntro es -> do
      es' <- mapM reduce es
      let sub = zip xs es'
      let _ :< body' = subst sub body
      reduce $ i :< body'
    _ -> return $ i :< NeutSigmaElim e' xs body
reduce (i :< NeutBoxElim e) = do
  e' <- reduce e
  case e' of
    _ :< NeutBoxIntro e'' -> reduce e''
    _                     -> return $ i :< NeutBoxElim e'
reduce (i :< NeutIndexElim e branchList) = do
  e' <- reduce e
  case e' of
    _ :< NeutIndexIntro x ->
      case lookup x branchList of
        Nothing ->
          lift $
          throwE $ "the index " ++ show x ++ " is not included in branchList"
        Just body -> reduce body
    _ -> return $ i :< NeutIndexElim e' branchList
reduce (meta :< NeutMu s e) = do
  e' <- reduce e
  return $ meta :< NeutMu s e'
reduce t = return t

subst :: Subst -> Neut -> Neut
subst sub (j :< NeutVar s) = fromMaybe (j :< NeutVar s) (lookup s sub)
subst _ (j :< NeutConst s) = j :< NeutConst s
subst sub (j :< NeutPi (s, tdom) tcod) = do
  let tdom' = subst sub tdom
  let tcod' = subst sub tcod -- note that we don't have to drop s from sub, thanks to rename.
  j :< NeutPi (s, tdom') tcod'
subst sub (j :< NeutPiIntro (s, tdom) body) = do
  let tdom' = subst sub tdom
  let body' = subst sub body
  j :< NeutPiIntro (s, tdom') body'
subst sub (j :< NeutPiElim e1 e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutPiElim e1' e2'
subst sub (j :< NeutSigma xts tcod) = do
  let (xs, ts) = unzip xts
  let ts' = map (subst sub) ts
  let tcod' = subst sub tcod
  j :< NeutSigma (zip xs ts') tcod'
subst sub (j :< NeutSigmaIntro es) = j :< NeutSigmaIntro (map (subst sub) es)
subst sub (j :< NeutSigmaElim e1 xs e2) = do
  let e1' = subst sub e1
  let e2' = subst sub e2
  j :< NeutSigmaElim e1' xs e2'
subst sub (j :< NeutBox e) = do
  let e' = subst sub e
  j :< NeutBox e'
subst sub (j :< NeutBoxIntro e) = do
  let e' = subst sub e
  j :< NeutBoxIntro e'
subst sub (j :< NeutBoxElim e) = do
  let e' = subst sub e
  j :< NeutBoxElim e'
subst _ (j :< NeutIndex x) = j :< NeutIndex x
subst _ (j :< NeutIndexIntro l) = j :< NeutIndexIntro l
subst sub (j :< NeutIndexElim e branchList) = do
  let e' = subst sub e
  let branchList' = map (\(l, e) -> (l, subst sub e)) branchList
  j :< NeutIndexElim e' branchList'
subst _ (j :< NeutUniv i) = j :< NeutUniv i
subst sub (j :< NeutMu x e) = do
  let e' = subst sub e
  j :< NeutMu x e'
subst sub (j :< NeutHole s) = fromMaybe (j :< NeutHole s) (lookup s sub)

findInvVar :: Subst -> Identifier -> Maybe Identifier
findInvVar [] _ = Nothing
findInvVar ((y, _ :< NeutVar x):rest) x'
  | x == x' =
    if not (any (/= y) $ findInvVar' rest x')
      then Just y
      else Nothing
findInvVar ((_, _):rest) i = findInvVar rest i

findInvVar' :: Subst -> Identifier -> [Identifier]
findInvVar' [] _ = []
findInvVar' ((z, _ :< NeutVar x):rest) x'
  | x /= x' = z : findInvVar' rest x'
findInvVar' (_:rest) x' = findInvVar' rest x'

invSubst :: Subst -> Neut -> Maybe Neut
invSubst sub (j :< NeutVar s) =
  case findInvVar sub s of
    Nothing -> Nothing
    Just x  -> return $ j :< NeutVar x
invSubst _ (j :< NeutConst s) = return $ j :< NeutConst s
invSubst sub (j :< NeutPi (s, tdom) tcod) = do
  tdom' <- invSubst sub tdom
  tcod' <- invSubst sub tcod -- note that we don't have to drop s from sub, thanks to rename.
  return $ j :< NeutPi (s, tdom') tcod'
invSubst sub (j :< NeutPiIntro (s, tdom) body) = do
  tdom' <- invSubst sub tdom
  body' <- invSubst sub body
  return $ j :< NeutPiIntro (s, tdom') body'
invSubst sub (j :< NeutPiElim e1 e2) = do
  e1' <- invSubst sub e1
  e2' <- invSubst sub e2
  return $ j :< NeutPiElim e1' e2'
invSubst sub (j :< NeutSigma xts tcod) = do
  let (xs, ts) = unzip xts
  ts' <- mapM (invSubst sub) ts
  tcod' <- invSubst sub tcod
  return $ j :< NeutSigma (zip xs ts') tcod'
invSubst sub (j :< NeutSigmaIntro es) = do
  es' <- mapM (invSubst sub) es
  return $ j :< NeutSigmaIntro es'
invSubst sub (j :< NeutSigmaElim e1 xs e2) = do
  e1' <- invSubst sub e1
  e2' <- invSubst sub e2
  return $ j :< NeutSigmaElim e1' xs e2'
invSubst sub (j :< NeutBox e) = do
  e' <- invSubst sub e
  return $ j :< NeutBox e'
invSubst sub (j :< NeutBoxIntro e) = do
  e' <- invSubst sub e
  return $ j :< NeutBoxIntro e'
invSubst sub (j :< NeutBoxElim e) = do
  e' <- invSubst sub e
  return $ j :< NeutBoxElim e'
invSubst _ (j :< NeutIndex x) = return $ j :< NeutIndex x
invSubst _ (j :< NeutIndexIntro l) = return $ j :< NeutIndexIntro l
invSubst sub (j :< NeutIndexElim e branchList) = do
  e' <- invSubst sub e
  let (ls, es) = unzip branchList
  es' <- mapM (invSubst sub) es
  return $ j :< NeutIndexElim e' (zip ls es')
invSubst _ (j :< NeutUniv i) = return $ j :< NeutUniv i
invSubst sub (j :< NeutMu x e) = do
  e' <- invSubst sub e
  return $ j :< NeutMu x e'
invSubst sub (j :< NeutHole s) =
  case findInvVar sub s of
    Nothing -> Nothing
    Just x  -> return $ j :< NeutHole x
  -- undefined --fromMaybe (j :< NeutHole s) (lookup s sub)

type SubstIdent = [(Identifier, Identifier)]

substIdent :: SubstIdent -> Identifier -> Identifier
substIdent sub x = fromMaybe x (lookup x sub)

compose :: Subst -> Subst -> Subst
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (subst s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'
