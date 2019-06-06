module Data.Term where

import           Data.Basic

data Term
  = TermVar Identifier
  | TermConst Identifier
  | TermPiIntro Identifier
                Term
  | TermPiElim Term
               Term
  | TermSigmaIntro [Term]
  | TermSigmaElim Term
                  [Identifier]
                  Term
  | TermIndexIntro Index
                   LowType
  | TermIndexElim Term
                  [(Index, Term)]
  deriving (Show)
