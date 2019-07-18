module Data.Term where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Level
  = LevelInt Term -- Int (EpsilonIntro)
  | LevelInfinity
  deriving (Show)

data Term
  = TermUpsilon Identifier
  | TermEpsilonIntro Literal
                     LowType
  | TermEpsilonElim Identifier
                    Term
                    [(Case, Term)]
  | TermPiIntro Level
                [Identifier]
                Term
  | TermPiElim Term
               [Term]
  | TermConstElim Identifier
                  [Term]
  | TermSigmaIntro Level
                   [Term]
  | TermSigmaElim [Identifier]
                  Term
                  Term
  | TermTauIntro Term
  | TermTauElim Term
  | TermConst Identifier
  deriving (Show)

type SubstTerm = [(Identifier, Term)]

substTerm :: SubstTerm -> Term -> Term
substTerm sub (TermUpsilon s) = fromMaybe (TermUpsilon s) (lookup s sub)
substTerm _ (TermEpsilonIntro l meta) = TermEpsilonIntro l meta
substTerm sub (TermEpsilonElim x e branchList) = do
  let e' = substTerm sub e
  let (labelList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substTerm sub') es
  TermEpsilonElim x e' $ zip labelList es'
substTerm sub (TermPiIntro s xs body) = do
  let s' = substLevel sub s
  let sub' = filter (\(k, _) -> k `notElem` xs) sub
  let body' = substTerm sub' body
  TermPiIntro s' xs body'
substTerm sub (TermPiElim e es) = do
  let e' = substTerm sub e
  let es' = map (substTerm sub) es
  TermPiElim e' es'
substTerm sub (TermConstElim x es) = do
  let es' = map (substTerm sub) es
  TermConstElim x es'
substTerm sub (TermSigmaIntro s es) = do
  let s' = substLevel sub s
  let es' = map (substTerm sub) es
  TermSigmaIntro s' es'
substTerm sub (TermSigmaElim xs e1 e2) = do
  let e1' = substTerm sub e1
  let sub' = filter (\(k, _) -> k `notElem` xs) sub
  let e2' = substTerm sub' e2
  TermSigmaElim xs e1' e2'
substTerm sub (TermTauIntro e) = TermTauIntro $ substTerm sub e
substTerm sub (TermTauElim e) = TermTauElim $ substTerm sub e
substTerm _ (TermConst x) = TermConst x

substLevel :: SubstTerm -> Level -> Level
substLevel sub (LevelInt e) = LevelInt $ substTerm sub e
substLevel _ LevelInfinity  = LevelInfinity
