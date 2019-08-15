module Data.Term where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Term
  = TermUpsilon Identifier
  | TermTheta Identifier
  | TermEpsilonIntro Literal
                     LowType
  | TermEpsilonElim Identifier
                    Term
                    [(Case, Term)]
  | TermPiIntro [Identifier]
                Term
  | TermPiElim Term
               [Term]
  | TermThetaElim Identifier
                  [Term]
  | TermSigmaIntro [Term]
  | TermSigmaElim [Identifier]
                  Term
                  Term
  deriving (Show)

type SubstTerm = [(Identifier, Term)]

substTerm :: SubstTerm -> Term -> Term
substTerm _ (TermTheta x) = TermTheta x
substTerm sub (TermUpsilon s) = fromMaybe (TermUpsilon s) (lookup s sub)
substTerm _ (TermEpsilonIntro l meta) = TermEpsilonIntro l meta
substTerm sub (TermEpsilonElim x e branchList) = do
  let e' = substTerm sub e
  let (labelList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substTerm sub') es
  TermEpsilonElim x e' $ zip labelList es'
substTerm sub (TermPiIntro xs body) = do
  let sub' = filter (\(k, _) -> k `notElem` xs) sub
  let body' = substTerm sub' body
  TermPiIntro xs body'
substTerm sub (TermPiElim e es) = do
  let e' = substTerm sub e
  let es' = map (substTerm sub) es
  TermPiElim e' es'
substTerm sub (TermThetaElim x es) = do
  let es' = map (substTerm sub) es
  TermThetaElim x es'
substTerm sub (TermSigmaIntro es) = do
  let es' = map (substTerm sub) es
  TermSigmaIntro es'
substTerm sub (TermSigmaElim xs e1 e2) = do
  let e1' = substTerm sub e1
  let sub' = filter (\(k, _) -> k `notElem` xs) sub
  let e2' = substTerm sub' e2
  TermSigmaElim xs e1' e2'
