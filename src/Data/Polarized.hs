module Data.Polarized where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Pos
  = PosVar Identifier
  | PosConst Identifier
  | PosSigmaIntro [Pos]
  | PosIndexIntro Literal
                  LowType
  deriving (Show)

data Neg
  = NegPiElimDownElim Pos
                      [Pos]
  | NegConstElim Constant
                 [Pos]
  | NegSigmaElim [Identifier]
                 Pos
                 Neg
  | NegIndexElim Pos
                 [(Case, Neg)]
  | NegUpIntro Pos
  | NegUpElim Identifier
              Neg
              Neg
  deriving (Show)

varPos :: Pos -> [Identifier]
varPos (PosVar s)          = [s]
varPos (PosConst _)        = []
varPos (PosSigmaIntro vs)  = concatMap varPos vs
varPos (PosIndexIntro _ _) = []

varNeg :: Neg -> [Identifier]
varNeg (NegPiElimDownElim v vs) = varPos v ++ concatMap varPos vs
varNeg (NegSigmaElim xs v e) = do
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
varNeg (NegConstElim _ vs) = concatMap varPos vs

type SubstPos = [(Identifier, Pos)]

substPos :: SubstPos -> Pos -> Pos
substPos sub (PosVar s) = fromMaybe (PosVar s) (lookup s sub)
substPos _ (PosConst s) = PosConst s
substPos sub (PosSigmaIntro vs) = do
  let vs' = map (substPos sub) vs
  PosSigmaIntro vs'
substPos _ (PosIndexIntro l t) = PosIndexIntro l t

substNeg :: SubstPos -> Neg -> Neg
substNeg sub (NegPiElimDownElim v vs) = do
  let v1' = substPos sub v
  let v2' = map (substPos sub) vs
  NegPiElimDownElim v1' v2'
substNeg sub (NegSigmaElim xs v e) = do
  let v' = substPos sub v
  let sub' = filter (\(x, _) -> x `notElem` xs) sub
  let e' = substNeg sub' e
  NegSigmaElim xs v' e'
substNeg sub (NegIndexElim v branchList) = do
  let v' = substPos sub v
  let branchList' = map (\(l, e) -> (l, substNeg sub e)) branchList
  NegIndexElim v' branchList'
substNeg sub (NegUpIntro v) = NegUpIntro $ substPos sub v
substNeg sub (NegUpElim x e1 e2) = do
  let e1' = substNeg sub e1
  let sub' = filter (\(y, _) -> x /= y) sub
  let e2' = substNeg sub' e2
  NegUpElim x e1' e2'
substNeg sub (NegConstElim x vs) = NegConstElim x $ map (substPos sub) vs
