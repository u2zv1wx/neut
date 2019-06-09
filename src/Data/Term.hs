module Data.Term where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Term
  = TermVar Identifier
  | TermConst Identifier
  | TermPiIntro Identifier
                Term
  | TermPiElim Term
               Term
  | TermConstElim Identifier
                  [Term]
  | TermSigmaIntro [Term]
  | TermSigmaElim Term
                  [Identifier]
                  Term
  | TermIndexIntro Index
                   LowType
  | TermIndexElim Term
                  [(Index, Term)]
  deriving (Show)

type SubstTerm = [(Identifier, Term)]

substTerm :: SubstTerm -> Term -> Term
substTerm sub (TermVar s) = fromMaybe (TermVar s) (lookup s sub)
substTerm _ (TermConst x) = TermConst x
substTerm sub (TermPiIntro s body) = do
  let sub' = filter (\(x, _) -> x /= s) sub
  let body' = substTerm sub' body
  TermPiIntro s body'
substTerm sub (TermPiElim e1 e2) = do
  let e1' = substTerm sub e1
  let e2' = substTerm sub e2
  TermPiElim e1' e2'
substTerm sub (TermConstElim x es) = do
  let es' = map (substTerm sub) es
  TermConstElim x es'
substTerm sub (TermSigmaIntro es) = TermSigmaIntro (map (substTerm sub) es)
substTerm sub (TermSigmaElim e1 xs e2) = do
  let e1' = substTerm sub e1
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e2' = substTerm sub' e2
  TermSigmaElim e1' xs e2'
substTerm _ (TermIndexIntro l meta) = TermIndexIntro l meta
substTerm sub (TermIndexElim e branchList) = do
  let e' = substTerm sub e
  let (labelList, es) = unzip branchList
  let es' = map (substTerm sub) es
  TermIndexElim e' $ zip labelList es'

toTermPiElimSeq :: Term -> (Term, [Term])
toTermPiElimSeq (TermPiElim e1 e2) = do
  let (fun, xs) = toTermPiElimSeq e1
  (fun, xs ++ [e2])
toTermPiElimSeq c = (c, [])

fromTermPiElimSeq :: (Term, [Term]) -> Term
fromTermPiElimSeq (term, [])   = term
fromTermPiElimSeq (term, v:xs) = fromTermPiElimSeq (TermPiElim term v, xs)
