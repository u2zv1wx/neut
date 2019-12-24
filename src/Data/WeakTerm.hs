{-# LANGUAGE FlexibleContexts #-}

module Data.WeakTerm where

import Numeric.Half

import Data.Basic

data WeakTerm
  = WeakTermTau
  | WeakTermTheta Identifier
  | WeakTermUpsilon Identifier
  | WeakTermPi [IdentifierPlus] WeakTermPlus
  | WeakTermPiIntro [IdentifierPlus] WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  | WeakTermMu IdentifierPlus WeakTermPlus
  | WeakTermZeta Identifier
  | WeakTermIntS IntSize Integer
  | WeakTermIntU IntSize Integer
  | WeakTermInt Integer
  | WeakTermFloat16 Half
  | WeakTermFloat32 Float
  | WeakTermFloat64 Double
  | WeakTermFloat Double
  | WeakTermEnum EnumType
  | WeakTermEnumIntro EnumValue
  | WeakTermEnumElim WeakTermPlus [(Case, WeakTermPlus)]
  | WeakTermArray ArrayKind WeakTermPlus WeakTermPlus
  | WeakTermArrayIntro ArrayKind [(EnumValue, WeakTermPlus)]
  | WeakTermArrayElim ArrayKind WeakTermPlus WeakTermPlus
  deriving (Show)

data WeakMeta
  = WeakMetaTerminal (Maybe Loc)
  | WeakMetaNonTerminal (Either Identifier WeakTermPlus) (Maybe Loc)
  -- deriving (Show)

instance Show WeakMeta where
  show _ = "_"

type WeakTermPlus = (WeakMeta, WeakTerm)

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTermPlus)

varWeakTermPlus :: WeakTermPlus -> ([Identifier], [Hole])
varWeakTermPlus (_, WeakTermTau) = ([], [])
varWeakTermPlus (_, WeakTermTheta _) = ([], [])
varWeakTermPlus (_, WeakTermUpsilon x) = ([x], [])
varWeakTermPlus (_, WeakTermPi xts t) = varWeakTermPlusBindings xts [t]
varWeakTermPlus (_, WeakTermPiIntro xts e) = varWeakTermPlusBindings xts [e]
varWeakTermPlus (_, WeakTermPiElim e es) =
  pairwiseConcat $ varWeakTermPlus e : map varWeakTermPlus es
varWeakTermPlus (_, WeakTermMu ut e) = varWeakTermPlusBindings [ut] [e]
varWeakTermPlus (_, WeakTermZeta h) = ([], [h])
varWeakTermPlus (_, WeakTermIntS _ _) = ([], [])
varWeakTermPlus (_, WeakTermIntU _ _) = ([], [])
varWeakTermPlus (_, WeakTermInt _) = ([], [])
varWeakTermPlus (_, WeakTermFloat16 _) = ([], [])
varWeakTermPlus (_, WeakTermFloat32 _) = ([], [])
varWeakTermPlus (_, WeakTermFloat64 _) = ([], [])
varWeakTermPlus (_, WeakTermFloat _) = ([], [])
varWeakTermPlus (_, WeakTermEnum _) = ([], [])
varWeakTermPlus (_, WeakTermEnumIntro _) = ([], [])
varWeakTermPlus (_, WeakTermEnumElim e branchList) = do
  let xhs = varWeakTermPlus e
  let xhss = map (\(_, body) -> varWeakTermPlus body) branchList
  pairwiseConcat (xhs : xhss)
varWeakTermPlus (_, WeakTermArray _ e1 e2) =
  pairwiseConcat $ [varWeakTermPlus e1, varWeakTermPlus e2]
varWeakTermPlus (_, WeakTermArrayIntro _ les) = do
  let xhss = map (\(_, body) -> varWeakTermPlus body) les
  pairwiseConcat xhss
varWeakTermPlus (_, WeakTermArrayElim _ e1 e2) =
  pairwiseConcat $ [varWeakTermPlus e1, varWeakTermPlus e2]

varWeakTermPlusBindings ::
     [IdentifierPlus] -> [WeakTermPlus] -> ([Identifier], [Identifier])
varWeakTermPlusBindings [] es = pairwiseConcat $ map varWeakTermPlus es
varWeakTermPlusBindings ((x, t):xts) es = do
  let (xs1, hs1) = varWeakTermPlus t
  let (xs2, hs2) = varWeakTermPlusBindings xts es
  (xs1 ++ filter (/= x) xs2, hs1 ++ hs2)

varWeakMeta :: WeakMeta -> ([Identifier], [Hole])
varWeakMeta (WeakMetaTerminal _) = ([], [])
varWeakMeta (WeakMetaNonTerminal (Right t) _) = varWeakTermPlus t
varWeakMeta (WeakMetaNonTerminal (Left _) _) = undefined

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

isReducible :: WeakTermPlus -> Bool
isReducible (_, WeakTermTau) = False
isReducible (_, WeakTermTheta _) = False
isReducible (_, WeakTermUpsilon _) = False
isReducible (_, WeakTermPi _ _) = False
isReducible (_, WeakTermPiIntro {}) = False
isReducible (_, WeakTermPiElim (_, WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_, WeakTermPiElim (_, WeakTermMu _ _) _) = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntS _ _), (_, WeakTermIntS _ _)])
  | Just (LowTypeIntS _, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntU _ _), (_, WeakTermIntU _ _)])
  | Just (LowTypeIntU _, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat16 _), (_, WeakTermFloat16 _)])
  | Just (LowTypeFloat FloatSize16, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat32 _), (_, WeakTermFloat32 _)])
  | Just (LowTypeFloat FloatSize32, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat64 _), (_, WeakTermFloat64 _)])
  | Just (LowTypeFloat FloatSize64, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim e es) = isReducible e || any isReducible es
isReducible (_, WeakTermMu _ _) = False
isReducible (_, WeakTermZeta _) = False
isReducible (_, WeakTermIntS _ _) = False
isReducible (_, WeakTermIntU _ _) = False
isReducible (_, WeakTermInt _) = False
isReducible (_, WeakTermFloat16 _) = False
isReducible (_, WeakTermFloat32 _) = False
isReducible (_, WeakTermFloat64 _) = False
isReducible (_, WeakTermFloat _) = False
isReducible (_, WeakTermEnum _) = False
isReducible (_, WeakTermEnumIntro _) = False
isReducible (_, WeakTermEnumElim (_, WeakTermEnumIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseValue l `elem` caseList || CaseDefault `elem` caseList
isReducible (_, WeakTermEnumElim e _) = isReducible e
isReducible (_, WeakTermArray {}) = False
isReducible (_, WeakTermArrayIntro _ les) = any isReducible $ map snd les
isReducible (_, WeakTermArrayElim _ (_, WeakTermArrayIntro _ les) (_, WeakTermEnumIntro l))
  | l `elem` map fst les = True
isReducible (_, WeakTermArrayElim _ e1 e2) = isReducible e1 || isReducible e2

isValue :: WeakTermPlus -> Bool
isValue (_, WeakTermTau) = True
isValue (_, WeakTermUpsilon _) = True
isValue (_, WeakTermPi {}) = True
isValue (_, WeakTermPiIntro {}) = True
isValue (_, WeakTermIntS _ _) = True
isValue (_, WeakTermIntU _ _) = True
isValue (_, WeakTermInt _) = True
isValue (_, WeakTermFloat16 _) = True
isValue (_, WeakTermFloat32 _) = True
isValue (_, WeakTermFloat64 _) = True
isValue (_, WeakTermFloat _) = True
isValue (_, WeakTermEnum _) = True
isValue (_, WeakTermEnumIntro _) = True
isValue (_, WeakTermArray {}) = True
isValue (_, WeakTermArrayIntro _ les) = all isValue $ map snd les
isValue _ = False
