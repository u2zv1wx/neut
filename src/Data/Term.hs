{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data.Term where

import           Control.Comonad.Cofree
import           Control.Monad          (forM)
import           Data.Maybe             (fromMaybe)
import           Text.Show.Deriving

import           Data.Basic

data TermF a
  = TermTau
  | TermTheta Identifier
  | TermUpsilon Identifier
  | TermEpsilon Identifier
  | TermEpsilonIntro Literal
  | TermEpsilonElim (Identifier, a)
                    a
                    [(Case, a)]
  | TermPi [(Identifier, a)]
  | TermPiIntro [(Identifier, a)]
                a
  | TermPiElim a
               [a]
  | TermSigma [(Identifier, a)]
  | TermSigmaIntro [a]
  | TermSigmaElim [(Identifier, a)]
                  a
                  a
  | TermMu (Identifier, a)
           a

type Term = Cofree TermF Meta

data Meta
  = MetaTerminal (Maybe (Int, Int))
  | MetaNonTerminal Term
                    (Maybe (Int, Int))

$(deriveShow1 ''TermF)

deriving instance Show Meta

type SubstTerm = [(Identifier, Term)]

type IdentifierPlus = (Identifier, Term)

varTerm :: Term -> [Identifier]
varTerm (_ :< TermTau) = []
varTerm (_ :< TermTheta _) = []
varTerm (_ :< TermUpsilon x) = [x]
varTerm (_ :< TermEpsilon _) = []
varTerm (_ :< TermEpsilonIntro _) = []
varTerm (_ :< TermEpsilonElim (x, t) e branchList) = do
  let xs1 = varTerm t
  let xs2 = varTerm e
  xss <-
    forM branchList $ \(_, body) -> do
      let xs = varTerm body
      return $ filter (/= x) xs
  xs1 ++ xs2 ++ concat xss
varTerm (_ :< TermPi xts) = varTermBindings xts []
varTerm (_ :< TermPiIntro xts e) = varTermBindings xts [e]
varTerm (_ :< TermPiElim e es) = varTerm e ++ concatMap varTerm es
varTerm (_ :< TermSigma xts) = varTermBindings xts []
varTerm (_ :< TermSigmaIntro es) = concatMap varTerm es
varTerm (_ :< TermSigmaElim us e1 e2) = varTerm e1 ++ varTermBindings us [e2]
varTerm (_ :< TermMu ut e) = varTermBindings [ut] [e]

varTermBindings :: [IdentifierPlus] -> [Term] -> [Identifier]
varTermBindings [] es = concatMap varTerm es
varTermBindings ((x, t):xts) es = do
  let xs1 = varTerm t
  let xs2 = varTermBindings xts es
  xs1 ++ filter (/= x) xs2

substTerm :: SubstTerm -> Term -> Term
substTerm _ (m :< TermTau) = m :< TermTau
substTerm _ (m :< TermTheta t) = m :< TermTheta t
substTerm sub (m :< TermUpsilon x) =
  fromMaybe (m :< TermUpsilon x) (lookup x sub)
substTerm _ (m :< TermEpsilon x) = m :< TermEpsilon x
substTerm _ (m :< TermEpsilonIntro l) = m :< TermEpsilonIntro l
substTerm sub (m :< TermEpsilonElim (x, t) e branchList) = do
  let t' = substTerm sub t
  let e' = substTerm sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substTerm sub') es
  m :< TermEpsilonElim (x, t') e' (zip caseList es')
substTerm sub (m :< TermPi xts) = do
  let xts' = substTermBindings sub xts
  m :< TermPi xts'
substTerm sub (m :< TermPiIntro xts body) = do
  let (xts', body') = substTermBindingsWithBody sub xts body
  m :< TermPiIntro xts' body'
substTerm sub (m :< TermPiElim e es) = do
  let e' = substTerm sub e
  let es' = map (substTerm sub) es
  m :< TermPiElim e' es'
substTerm sub (m :< TermSigma xts) = do
  let xts' = substTermBindings sub xts
  m :< TermSigma xts'
substTerm sub (m :< TermSigmaIntro es) = do
  let es' = map (substTerm sub) es
  m :< TermSigmaIntro es'
substTerm sub (m :< TermSigmaElim xts e1 e2) = do
  let e1' = substTerm sub e1
  let (xts', e2') = substTermBindingsWithBody sub xts e2
  m :< TermSigmaElim xts' e1' e2'
substTerm sub (m :< TermMu (x, t) e) = do
  let t' = substTerm sub t
  let e' = substTerm (filter (\(k, _) -> k /= x) sub) e
  m :< TermMu (x, t') e'

substTermBindings :: SubstTerm -> [IdentifierPlus] -> [IdentifierPlus]
substTermBindings _ [] = []
substTermBindings sub ((x, t):xts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let xts' = substTermBindings sub' xts
  (x, substTerm sub t) : xts'

substTermBindingsWithBody ::
     SubstTerm -> [IdentifierPlus] -> Term -> ([IdentifierPlus], Term)
substTermBindingsWithBody sub [] e = ([], substTerm sub e)
substTermBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substTermBindingsWithBody sub' xts e
  ((x, substTerm sub t) : xts', e')

isValue :: Term -> Bool
isValue (_ :< TermTau)            = True
isValue (_ :< TermUpsilon _)      = True
isValue (_ :< TermEpsilon _)      = True
isValue (_ :< TermEpsilonIntro _) = True
isValue (_ :< TermPi {})          = True
isValue (_ :< TermPiIntro {})     = True
isValue (_ :< TermSigma {})       = True
isValue (_ :< TermSigmaIntro es)  = all isValue es
isValue _                         = False
