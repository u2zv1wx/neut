module Data.PreTerm where

import Data.Maybe (fromMaybe)
import Numeric.Half

import Data.Basic

data PreTerm
  = PreTermTau
  | PreTermTheta Identifier
  | PreTermUpsilon Identifier
  | PreTermPi [IdentifierPlus] PreTermPlus
  | PreTermPiIntro [IdentifierPlus] PreTermPlus
  | PreTermPiElim PreTermPlus [PreTermPlus]
  | PreTermMu IdentifierPlus PreTermPlus
  | PreTermZeta Identifier
  | PreTermIntS IntSize Integer
  | PreTermIntU IntSize Integer
  | PreTermInt Integer
  | PreTermFloat16 Half
  | PreTermFloat32 Float
  | PreTermFloat64 Double
  | PreTermFloat Double
  | PreTermEnum EnumType
  | PreTermEnumIntro EnumValue
  | PreTermEnumElim PreTermPlus [(Case, PreTermPlus)]
  | PreTermArray ArrayKind PreTermPlus PreTermPlus
  | PreTermArrayIntro ArrayKind [(EnumValue, PreTermPlus)]
  | PreTermArrayElim ArrayKind PreTermPlus PreTermPlus
  deriving (Show)

type PreTermPlus = (PreMeta, PreTerm)

type SubstPreTerm = [(Identifier, PreTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, PreTermPlus)

data PreMeta
  = PreMetaTerminal (Maybe Loc)
  | PreMetaNonTerminal PreTermPlus (Maybe Loc)
  -- deriving (Show)

instance Show PreMeta where
  show _ = "_"

varPreTermPlus :: PreTermPlus -> ([Identifier], [Hole])
varPreTermPlus (m, PreTermTau) = varPreMeta m
varPreTermPlus (m, PreTermTheta _) = varPreMeta m
varPreTermPlus (m, PreTermUpsilon x) = do
  let xhs = varPreMeta m
  pairwiseConcat [([x], []), xhs]
varPreTermPlus (m, PreTermPi xts t) = do
  let xhs = varPreTermPlusBindings xts [t]
  let yhs = varPreMeta m
  pairwiseConcat [xhs, yhs]
varPreTermPlus (m, PreTermPiIntro xts e) = do
  let xhs = varPreTermPlusBindings xts [e]
  let yhs = varPreMeta m
  pairwiseConcat [xhs, yhs]
varPreTermPlus (m, PreTermPiElim e es) = do
  let xhs = varPreTermPlus e
  let yhss = map varPreTermPlus es
  let zhs = varPreMeta m
  pairwiseConcat $ xhs : zhs : yhss
varPreTermPlus (m, PreTermMu ut e) = do
  let xhs = varPreTermPlusBindings [ut] [e]
  let yhs = varPreMeta m
  pairwiseConcat [xhs, yhs]
varPreTermPlus (m, PreTermZeta h) = do
  let xhs = varPreMeta m
  pairwiseConcat [([], [h]), xhs]
varPreTermPlus (m, PreTermIntS _ _) = varPreMeta m
varPreTermPlus (m, PreTermIntU _ _) = varPreMeta m
varPreTermPlus (m, PreTermInt _) = varPreMeta m
varPreTermPlus (m, PreTermFloat16 _) = varPreMeta m
varPreTermPlus (m, PreTermFloat32 _) = varPreMeta m
varPreTermPlus (m, PreTermFloat64 _) = varPreMeta m
varPreTermPlus (m, PreTermFloat _) = varPreMeta m
varPreTermPlus (m, PreTermEnum _) = varPreMeta m
varPreTermPlus (m, PreTermEnumIntro _) = varPreMeta m
varPreTermPlus (m, PreTermEnumElim e les) = do
  let xhs = varPreTermPlus e
  let xhss = map (\(_, body) -> varPreTermPlus body) les
  let yhs = varPreMeta m
  pairwiseConcat $ xhs : yhs : xhss
varPreTermPlus (m, PreTermArray _ e1 e2) = do
  let xhs1 = varPreTermPlus e1
  let xhs2 = varPreTermPlus e2
  let xhs3 = varPreMeta m
  pairwiseConcat [xhs1, xhs2, xhs3]
varPreTermPlus (m, PreTermArrayIntro _ les) = do
  let xhs = varPreMeta m
  let xhss = map (\(_, body) -> varPreTermPlus body) les
  pairwiseConcat $ xhs : xhss
varPreTermPlus (m, PreTermArrayElim _ e1 e2) = do
  let xhs1 = varPreTermPlus e1
  let xhs2 = varPreTermPlus e2
  let xhs3 = varPreMeta m
  pairwiseConcat [xhs1, xhs2, xhs3]

varPreTermPlusBindings ::
     [IdentifierPlus] -> [PreTermPlus] -> ([Identifier], [Hole])
varPreTermPlusBindings [] es = do
  let xhss = map varPreTermPlus es
  pairwiseConcat xhss
varPreTermPlusBindings ((x, t):xts) es = do
  let (xs1, hs1) = varPreTermPlus t
  let (xs2, hs2) = varPreTermPlusBindings xts es
  (xs1 ++ filter (/= x) xs2, hs1 ++ hs2)

varPreMeta :: PreMeta -> ([Identifier], [Hole])
-- varPreMeta _ = ([], [])
varPreMeta (PreMetaTerminal _) = ([], [])
varPreMeta (PreMetaNonTerminal t _) = varPreTermPlus t

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substPreTermPlus :: SubstPreTerm -> PreTermPlus -> PreTermPlus
substPreTermPlus sub (m, PreTermTau) = do
  let m' = substPreMeta sub m
  (m', PreTermTau)
substPreTermPlus sub (m, PreTermTheta t) = do
  let m' = substPreMeta sub m
  (m', PreTermTheta t)
substPreTermPlus sub (m, PreTermUpsilon x) = do
  let m' = substPreMeta sub m
  fromMaybe (m', PreTermUpsilon x) (lookup x sub)
substPreTermPlus sub (m, PreTermPi xts t) = do
  let m' = substPreMeta sub m
  let (xts', t') = substPreTermPlusBindingsWithBody sub xts t
  (m', PreTermPi xts' t')
substPreTermPlus sub (m, PreTermPiIntro xts body) = do
  let m' = substPreMeta sub m
  let (xts', body') = substPreTermPlusBindingsWithBody sub xts body
  (m', PreTermPiIntro xts' body')
substPreTermPlus sub (m, PreTermPiElim e es) = do
  let m' = substPreMeta sub m
  let e' = substPreTermPlus sub e
  let es' = map (substPreTermPlus sub) es
  (m', PreTermPiElim e' es')
substPreTermPlus sub (m, PreTermMu (x, t) e) = do
  let m' = substPreMeta sub m
  let t' = substPreTermPlus sub t
  let e' = substPreTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m', PreTermMu (x, t') e')
substPreTermPlus sub (m, PreTermZeta s) = do
  let m' = substPreMeta sub m
  fromMaybe (m', PreTermZeta s) (lookup s sub)
substPreTermPlus sub (m, PreTermIntS size x) = do
  let m' = substPreMeta sub m
  (m', PreTermIntS size x)
substPreTermPlus sub (m, PreTermIntU size x) = do
  let m' = substPreMeta sub m
  (m', PreTermIntU size x)
substPreTermPlus sub (m, PreTermInt x) = do
  let m' = substPreMeta sub m
  (m', PreTermInt x)
substPreTermPlus sub (m, PreTermFloat16 x) = do
  let m' = substPreMeta sub m
  (m', PreTermFloat16 x)
substPreTermPlus sub (m, PreTermFloat32 x) = do
  let m' = substPreMeta sub m
  (m', PreTermFloat32 x)
substPreTermPlus sub (m, PreTermFloat64 x) = do
  let m' = substPreMeta sub m
  (m', PreTermFloat64 x)
substPreTermPlus sub (m, PreTermFloat x) = do
  let m' = substPreMeta sub m
  (m', PreTermFloat x)
substPreTermPlus sub (m, PreTermEnum x) = do
  let m' = substPreMeta sub m
  (m', PreTermEnum x)
substPreTermPlus sub (m, PreTermEnumIntro l) = do
  let m' = substPreMeta sub m
  (m', PreTermEnumIntro l)
substPreTermPlus sub (m, PreTermEnumElim e branchList) = do
  let m' = substPreMeta sub m
  let e' = substPreTermPlus sub e
  let (caseList, es) = unzip branchList
  let es' = map (substPreTermPlus sub) es
  (m', PreTermEnumElim e' (zip caseList es'))
substPreTermPlus sub (m, PreTermArray kind from to) = do
  let m' = substPreMeta sub m
  let from' = substPreTermPlus sub from
  let to' = substPreTermPlus sub to
  (m', PreTermArray kind from' to')
substPreTermPlus sub (m, PreTermArrayIntro kind les) = do
  let m' = substPreMeta sub m
  let (ls, es) = unzip les
  let es' = map (substPreTermPlus sub) es
  (m', PreTermArrayIntro kind (zip ls es'))
substPreTermPlus sub (m, PreTermArrayElim kind e1 e2) = do
  let m' = substPreMeta sub m
  let e1' = substPreTermPlus sub e1
  let e2' = substPreTermPlus sub e2
  (m', PreTermArrayElim kind e1' e2')

substPreTermPlusBindingsWithBody ::
     SubstPreTerm
  -> [IdentifierPlus]
  -> PreTermPlus
  -> ([IdentifierPlus], PreTermPlus)
substPreTermPlusBindingsWithBody sub [] e = do
  let e' = substPreTermPlus sub e
  ([], e')
substPreTermPlusBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substPreTermPlusBindingsWithBody sub' xts e
  let t' = substPreTermPlus sub t
  ((x, t') : xts', e')

substPreMeta :: SubstPreTerm -> PreMeta -> PreMeta
-- substPreMeta _ m = m
substPreMeta _ m@(PreMetaTerminal _) = m
substPreMeta sub (PreMetaNonTerminal t ml) =
  PreMetaNonTerminal (substPreTermPlus sub t) ml

isReducible :: PreTermPlus -> Bool
isReducible (_, PreTermTau) = False
isReducible (_, PreTermTheta _) = False
isReducible (_, PreTermUpsilon _) = False
isReducible (_, PreTermPi xts cod) =
  any isReducible (map snd xts) || isReducible cod
isReducible (_, PreTermPiIntro {}) = False
-- isReducible (_, PreTermPiElim (_, PreTermPiIntro xts _) es)
--   | length xts == length es
--   , all isValue es = True
isReducible (_, PreTermPiElim (_, PreTermPiIntro xts _) es)
  | length xts == length es = True -- 言語はpureなのでvalueじゃなくてもreduceを許す
-- isReducible (_, PreTermPiElim (_, PreTermMu _ _) es) = all isValue es -- muのときだけCBV的な挙動を要求する
isReducible (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermIntS _ _), (_, PreTermIntS _ _)])
  | Just (LowTypeIntS _, _) <- asBinaryOpMaybe c = True
isReducible (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermIntU _ _), (_, PreTermIntU _ _)])
  | Just (LowTypeIntU _, _) <- asBinaryOpMaybe c = True
isReducible (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermFloat16 _), (_, PreTermFloat16 _)])
  | Just (LowTypeFloat FloatSize16, _) <- asBinaryOpMaybe c = True
isReducible (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermFloat32 _), (_, PreTermFloat32 _)])
  | Just (LowTypeFloat FloatSize32, _) <- asBinaryOpMaybe c = True
isReducible (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermFloat64 _), (_, PreTermFloat64 _)])
  | Just (LowTypeFloat FloatSize64, _) <- asBinaryOpMaybe c = True
isReducible (_, PreTermPiElim e es) = isReducible e || any isReducible es
isReducible (_, PreTermMu _ _) = False
isReducible (_, PreTermZeta _) = False
isReducible (_, PreTermIntS _ _) = False
isReducible (_, PreTermIntU _ _) = False
isReducible (_, PreTermInt _) = False
isReducible (_, PreTermFloat16 _) = False
isReducible (_, PreTermFloat32 _) = False
isReducible (_, PreTermFloat64 _) = False
isReducible (_, PreTermFloat _) = False
isReducible (_, PreTermEnum _) = False
isReducible (_, PreTermEnumIntro _) = False
isReducible (_, PreTermEnumElim (_, PreTermEnumIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseValue l `elem` caseList || CaseDefault `elem` caseList
isReducible (_, PreTermEnumElim e _) = isReducible e
isReducible (_, PreTermArray {}) = False
isReducible (_, PreTermArrayIntro _ les) = any isReducible $ map snd les
isReducible (_, PreTermArrayElim _ (_, PreTermArrayIntro _ les) (_, PreTermEnumIntro l))
  | l `elem` map fst les = True
isReducible (_, PreTermArrayElim _ e1 e2) = isReducible e1 || isReducible e2

isValue :: PreTermPlus -> Bool
isValue (_, PreTermTau) = True
isValue (_, PreTermTheta _) = True
isValue (_, PreTermUpsilon _) = True
isValue (_, PreTermPi {}) = True
isValue (_, PreTermPiIntro {}) = True
isValue (_, PreTermIntS _ _) = True
isValue (_, PreTermIntU _ _) = True
isValue (_, PreTermInt _) = True
isValue (_, PreTermFloat16 _) = True
isValue (_, PreTermFloat32 _) = True
isValue (_, PreTermFloat64 _) = True
isValue (_, PreTermFloat _) = True
isValue (_, PreTermEnum _) = True
isValue (_, PreTermEnumIntro _) = True
isValue (_, PreTermArray {}) = True
isValue (_, PreTermArrayIntro _ les) = all isValue $ map snd les
isValue _ = False
