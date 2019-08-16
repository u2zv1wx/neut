module Data.Code where

import           Data.Maybe (fromMaybe)

import           Data.Basic

data Data
  = DataTau
  | DataTheta Identifier
  | DataUpsilon Identifier
  | DataEpsilon Identifier
  | DataEpsilonIntro Literal
                     LowType
  | DataDownPi [(Identifier, DataPlus)]
               CodePlus
  | DataSigma [(Identifier, DataPlus)]
              DataPlus
  | DataSigmaIntro [DataPlus]

data Code
  = CodeEpsilonElim (Identifier, DataPlus)
                    DataPlus
                    [(Case, CodePlus)]
  | CodePiElimDownElim DataPlus
                       [DataPlus]
  | CodeSigmaElim [(Identifier, DataPlus)]
                  DataPlus
                  CodePlus
  | CodeUp DataPlus
  | CodeUpIntro DataPlus
  | CodeUpElim (Identifier, DataPlus)
               CodePlus
               CodePlus
  -- | CodeConstElim Constant
  --                [DataPlus]

data DataMeta
  = DataMetaTerminal (Maybe (Int, Int))
  | DataMetaNonTerminal Data
                        (Maybe (Int, Int))

type CodeMeta = String -- data CodePlus =

type DataPlus = (DataMeta, Data)

type CodePlus = (CodeMeta, Code)
-- data Value =
--   Value DataMeta
--         Data
--   deriving (Show)
--   Comp CodeMeta
--        Code
--   deriving (Show)
-- varData :: Data -> [Identifier]
-- varData (DataUpsilon s)        = [s]
-- varData (DataConst _)          = []
-- varData (DataSigmaIntro vs)    = concatMap varData vs
-- varData (DataEpsilonIntro _ _) = []
-- varCode :: Code -> [Identifier]
-- varCode (CodePiElimDownElim v vs) = varData v ++ concatMap varData vs
-- varCode (CodeSigmaElim xs v e) = do
--   let vs1 = varData v
--   let vs2 = filter (`notElem` xs) $ varCode e
--   vs1 ++ vs2
-- varCode (CodeEpsilonElim v branchList) = do
--   let vs1 = varData v
--   let vs2 = concatMap (varCode . snd) branchList
--   vs1 ++ vs2
-- varCode (CodeUpIntro v) = varData v
-- varCode (CodeUpElim x e1 e2) = do
--   let vs1 = varCode e1
--   let vs2 = filter (/= x) $ varCode e2
--   vs1 ++ vs2
-- varCode (CodeConstElim _ vs) = concatMap varData vs
-- type SubstData = [(Identifier, Data)]
-- substData :: SubstData -> Data -> Data
-- substData sub (DataUpsilon s) = fromMaybe (DataUpsilon s) (lookup s sub)
-- substData _ (DataConst s) = DataConst s
-- substData sub (DataSigmaIntro vs) = do
--   let vs' = map (substData sub) vs
--   DataSigmaIntro vs'
-- substData _ (DataEpsilonIntro l t) = DataEpsilonIntro l t
-- substCode :: SubstData -> Code -> Code
-- substCode sub (CodePiElimDownElim v vs) = do
--   let v1' = substData sub v
--   let v2' = map (substData sub) vs
--   CodePiElimDownElim v1' v2'
-- substCode sub (CodeSigmaElim xs v e) = do
--   let v' = substData sub v
--   let sub' = filter (\(x, _) -> x `notElem` xs) sub
--   let e' = substCode sub' e
--   CodeSigmaElim xs v' e'
-- substCode sub (CodeEpsilonElim v branchList) = do
--   let v' = substData sub v
--   let branchList' = map (\(l, e) -> (l, substCode sub e)) branchList
--   CodeEpsilonElim v' branchList'
-- substCode sub (CodeUpIntro v) = CodeUpIntro $ substData sub v
-- substCode sub (CodeUpElim x e1 e2) = do
--   let e1' = substCode sub e1
--   let sub' = filter (\(y, _) -> x /= y) sub
--   let e2' = substCode sub' e2
--   CodeUpElim x e1' e2'
-- substCode sub (CodeConstElim x vs) = CodeConstElim x $ map (substData sub) vs
