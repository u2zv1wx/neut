module Util where

import Control.Monad.Except
import Control.Monad.Identity
import Control.Monad.Trans.Except

import Control.Comonad
import Control.Comonad.Cofree

import Control.Monad.State

import Data
import Reduce

import Data.Maybe (fromMaybe)

import qualified Text.Show.Pretty as Pr

import qualified Data.Map.Strict as Map

import Debug.Trace

import System.Directory
import System.FilePath

isLinear :: Identifier -> [Identifier] -> [Identifier]
isLinear x xs =
  if length (filter (== x) xs) == 1
    then []
    else [x]

foldML ::
     (Cofree f Identifier -> a -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldML _ e [] = return e
foldML f e (t:ts) = do
  let tmp = f e t
  i <- newName
  foldML f (i :< tmp) ts

foldMR ::
     (a -> Cofree f Identifier -> f (Cofree f Identifier))
  -> Cofree f Identifier
  -> [a]
  -> StateT Env (ExceptT String IO) (Cofree f Identifier)
foldMR _ e [] = return e
foldMR f e (t:ts) = do
  tmp <- foldMR f e ts
  let x = f t tmp
  i <- newName
  return $ i :< x

appFold :: Neut -> [Neut] -> WithEnv Neut
appFold e [] = return e
appFold e@(i :< _) (term:ts) = do
  t <- lookupTypeEnv' i
  case t of
    _ :< NeutPi _ tcod -> do
      meta <- newNameWith "meta"
      insTypeEnv meta tcod
      appFold (meta :< NeutPiElim e term) ts
    _ ->
      lift $ throwE $ "appfold. t:\n" ++ Pr.ppShow t ++ "\ne:\n" ++ Pr.ppShow e

appFold' :: Neut -> [Neut] -> WithEnv Neut
appFold' e [] = return e
appFold' e (term:ts) = do
  meta <- newNameWith "meta"
  appFold' (meta :< NeutPiElim e term) ts

bindFormalArgs' :: [Identifier] -> Neut -> WithEnv Neut
bindFormalArgs' [] terminal = return terminal
bindFormalArgs' (arg:xs) c = do
  tmp <- bindFormalArgs' xs c
  meta <- newNameWith "meta"
  h <- newNameWith "hole"
  holeMeta <- newNameWith "meta"
  return $ meta :< NeutPiIntro (arg, holeMeta :< NeutHole h) tmp

boxUniv :: WithEnv Neut
boxUniv = do
  univMeta <- newNameWith "meta"
  l <- newName
  return $ univMeta :< NeutUniv (UnivLevelHole l)

toVar1 :: Identifier -> Neut -> WithEnv Neut
toVar1 x t = do
  meta <- newNameWith "meta"
  insTypeEnv meta t
  return $ meta :< NeutVar x

toVar' :: Identifier -> WithEnv Neut
toVar' x = do
  meta <- newNameWith "meta"
  return $ meta :< NeutVar x

insDef :: Identifier -> Neut -> WithEnv (Maybe Neut)
insDef x body = do
  sub <- gets substitution
  modify (\e -> e {substitution = (x, body) : substitution e})
  return $ lookup x sub

compose :: Subst -> Subst -> Subst
compose s1 s2 = do
  let domS2 = map fst s2
  let codS2 = map snd s2
  let codS2' = map (subst s1) codS2
  let fromS1 = filter (\(ident, _) -> ident `notElem` domS2) s1
  fromS1 ++ zip domS2 codS2'

varPos :: Pos -> [Identifier]
varPos (PosVar s) = [s]
varPos (PosConst _) = []
varPos (PosSigmaIntro vs) = concatMap varPos vs
varPos (PosIndexIntro _ _) = []
varPos (PosDownIntro e) = varNeg e

varNeg :: Neg -> [Identifier]
varNeg (NegPiIntro x e) = filter (/= x) $ varNeg e
varNeg (NegPiElim e v) = varNeg e ++ varPos v
varNeg (NegSigmaElim v xs e) = do
  let vs1 = varPos v
  let vs2 = filter (`notElem` xs) $ varNeg e
  vs1 ++ vs2
varNeg (NegIndexElim v branchList) = do
  let vs1 = varPos v
  let vs2 = concatMap (varNeg . snd) branchList
  vs1 ++ vs2
varNeg (NegUpIntro v) = varPos v
varNeg (NegUpElim x e1 e2) = do
  let vs1 = varNeg e1
  let vs2 = filter (/= x) $ varNeg e2
  vs1 ++ vs2
varNeg (NegDownElim v) = varPos v
varNeg (NegConstElim _ vs) = concatMap varPos vs
