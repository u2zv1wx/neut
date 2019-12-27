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

varPreTermPlus :: PreTermPlus -> [Hole]
varPreTermPlus (m, PreTermTau) = varPreMeta m
varPreTermPlus (m, PreTermTheta _) = varPreMeta m
varPreTermPlus (m, PreTermUpsilon _) = do
  varPreMeta m
varPreTermPlus (m, PreTermPi xts t) = do
  let xhs = varPreTermPlusBindings xts [t]
  let yhs = varPreMeta m
  xhs ++ yhs
varPreTermPlus (m, PreTermPiIntro xts e) = do
  let xhs = varPreTermPlusBindings xts [e]
  let yhs = varPreMeta m
  xhs ++ yhs
varPreTermPlus (m, PreTermPiElim e es) = do
  let xhs = varPreTermPlus e
  let yhs = concatMap varPreTermPlus es
  let zhs = varPreMeta m
  xhs ++ yhs ++ zhs
varPreTermPlus (m, PreTermMu ut e) = do
  let xhs = varPreTermPlusBindings [ut] [e]
  let yhs = varPreMeta m
  xhs ++ yhs
varPreTermPlus (m, PreTermZeta h) = do
  let xhs = varPreMeta m
  h : xhs
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
  let yhs = concatMap (\(_, body) -> varPreTermPlus body) les
  let zhs = varPreMeta m
  xhs ++ yhs ++ zhs
varPreTermPlus (m, PreTermArray _ e1 e2) = do
  let xhs1 = varPreTermPlus e1
  let xhs2 = varPreTermPlus e2
  let xhs3 = varPreMeta m
  xhs1 ++ xhs2 ++ xhs3
varPreTermPlus (m, PreTermArrayIntro _ les) = do
  let xhs = varPreMeta m
  let yhs = concatMap (\(_, body) -> varPreTermPlus body) les
  xhs ++ yhs
varPreTermPlus (m, PreTermArrayElim _ e1 e2) = do
  let xhs1 = varPreTermPlus e1
  let xhs2 = varPreTermPlus e2
  let xhs3 = varPreMeta m
  xhs1 ++ xhs2 ++ xhs3

varPreTermPlusBindings :: [IdentifierPlus] -> [PreTermPlus] -> [Hole]
varPreTermPlusBindings [] es = do
  concatMap varPreTermPlus es
varPreTermPlusBindings ((x, t):xts) es = do
  let hs1 = varPreTermPlus t
  let hs2 = varPreTermPlusBindings xts es
  hs1 ++ filter (/= x) hs2

varPreMeta :: PreMeta -> [Hole]
varPreMeta (PreMetaTerminal _) = []
varPreMeta (PreMetaNonTerminal t _) = varPreTermPlus t

holePreTermPlus :: PreTermPlus -> [Hole]
holePreTermPlus (m, PreTermTau) = holePreMeta m
holePreTermPlus (m, PreTermTheta _) = holePreMeta m
holePreTermPlus (m, PreTermUpsilon _) = do
  holePreMeta m
holePreTermPlus (m, PreTermPi xts t) = do
  let xhs = holePreTermPlusBindings xts [t]
  let yhs = holePreMeta m
  xhs ++ yhs
holePreTermPlus (m, PreTermPiIntro xts e) = do
  let xhs = holePreTermPlusBindings xts [e]
  let yhs = holePreMeta m
  xhs ++ yhs
holePreTermPlus (m, PreTermPiElim e es) = do
  let xhs = holePreTermPlus e
  let yhs = concatMap holePreTermPlus es
  let zhs = holePreMeta m
  xhs ++ yhs ++ zhs
holePreTermPlus (m, PreTermMu ut e) = do
  let xhs = holePreTermPlusBindings [ut] [e]
  let yhs = holePreMeta m
  xhs ++ yhs
holePreTermPlus (m, PreTermZeta h) = do
  let xhs = holePreMeta m
  h : xhs
holePreTermPlus (m, PreTermIntS _ _) = holePreMeta m
holePreTermPlus (m, PreTermIntU _ _) = holePreMeta m
holePreTermPlus (m, PreTermInt _) = holePreMeta m
holePreTermPlus (m, PreTermFloat16 _) = holePreMeta m
holePreTermPlus (m, PreTermFloat32 _) = holePreMeta m
holePreTermPlus (m, PreTermFloat64 _) = holePreMeta m
holePreTermPlus (m, PreTermFloat _) = holePreMeta m
holePreTermPlus (m, PreTermEnum _) = holePreMeta m
holePreTermPlus (m, PreTermEnumIntro _) = holePreMeta m
holePreTermPlus (m, PreTermEnumElim e les) = do
  let xhs = holePreTermPlus e
  let yhs = concatMap (\(_, body) -> holePreTermPlus body) les
  let zhs = holePreMeta m
  xhs ++ yhs ++ zhs
holePreTermPlus (m, PreTermArray _ e1 e2) = do
  let xhs1 = holePreTermPlus e1
  let xhs2 = holePreTermPlus e2
  let xhs3 = holePreMeta m
  xhs1 ++ xhs2 ++ xhs3
holePreTermPlus (m, PreTermArrayIntro _ les) = do
  let xhs = holePreMeta m
  let yhs = concatMap (\(_, body) -> holePreTermPlus body) les
  xhs ++ yhs
holePreTermPlus (m, PreTermArrayElim _ e1 e2) = do
  let xhs1 = holePreTermPlus e1
  let xhs2 = holePreTermPlus e2
  let xhs3 = holePreMeta m
  xhs1 ++ xhs2 ++ xhs3

holePreTermPlusBindings :: [IdentifierPlus] -> [PreTermPlus] -> [Hole]
holePreTermPlusBindings [] es = do
  concatMap holePreTermPlus es
holePreTermPlusBindings ((_, t):xts) es = do
  let hs1 = holePreTermPlus t
  let hs2 = holePreTermPlusBindings xts es
  hs1 ++ hs2

holePreMeta :: PreMeta -> [Hole]
holePreMeta (PreMetaTerminal _) = []
holePreMeta (PreMetaNonTerminal t _) = holePreTermPlus t

substPreTermPlus :: SubstPreTerm -> PreTermPlus -> PreTermPlus
substPreTermPlus sub (m, PreTermTau) = do
  let m' = substPreMeta sub m
  (m', PreTermTau)
substPreTermPlus sub (m, PreTermTheta t) = do
  let m' = substPreMeta sub m
  (m', PreTermTheta t)
substPreTermPlus sub (m, PreTermUpsilon x) = do
  let m' = substPreMeta sub m
  -- このときlookupの結果のmetaとm'とが同一であるって情報を保持する必要があるのでは？
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
substPreMeta _ m@(PreMetaTerminal _) = m
substPreMeta sub (PreMetaNonTerminal t ml) =
  PreMetaNonTerminal (substPreTermPlus sub t) ml

isReduciblePreTerm :: PreTermPlus -> Bool
isReduciblePreTerm (m, PreTermTau) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermTheta _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermUpsilon _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermPi xts cod) =
  isReduciblePreMeta m ||
  any isReduciblePreTerm (map snd xts) || isReduciblePreTerm cod
isReduciblePreTerm (m, PreTermPiIntro xts e) =
  isReduciblePreMeta m ||
  any isReduciblePreTerm (map snd xts) || isReduciblePreTerm e
isReduciblePreTerm (_, PreTermPiElim (_, PreTermPiIntro xts _) es)
  | length xts == length es = True
isReduciblePreTerm (_, PreTermPiElim (_, PreTermMu _ _) es) = all isValue es -- muのときだけCBV的な挙動を要求する
isReduciblePreTerm (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermIntS _ _), (_, PreTermIntS _ _)])
  | Just (LowTypeIntS _, _) <- asBinaryOpMaybe c = True
isReduciblePreTerm (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermIntU _ _), (_, PreTermIntU _ _)])
  | Just (LowTypeIntU _, _) <- asBinaryOpMaybe c = True
isReduciblePreTerm (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermFloat16 _), (_, PreTermFloat16 _)])
  | Just (LowTypeFloat FloatSize16, _) <- asBinaryOpMaybe c = True
isReduciblePreTerm (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermFloat32 _), (_, PreTermFloat32 _)])
  | Just (LowTypeFloat FloatSize32, _) <- asBinaryOpMaybe c = True
isReduciblePreTerm (_, PreTermPiElim (_, PreTermTheta c) [(_, PreTermFloat64 _), (_, PreTermFloat64 _)])
  | Just (LowTypeFloat FloatSize64, _) <- asBinaryOpMaybe c = True
isReduciblePreTerm (m, PreTermPiElim e es) =
  isReduciblePreMeta m || isReduciblePreTerm e || any isReduciblePreTerm es
isReduciblePreTerm (m, PreTermMu (_, t) e) =
  isReduciblePreMeta m || isReduciblePreTerm t || isReduciblePreTerm e
isReduciblePreTerm (m, PreTermZeta _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermIntS _ _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermIntU _ _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermInt _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermFloat16 _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermFloat32 _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermFloat64 _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermFloat _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermEnum _) = isReduciblePreMeta m
isReduciblePreTerm (m, PreTermEnumIntro _) = isReduciblePreMeta m
isReduciblePreTerm (_, PreTermEnumElim (_, PreTermEnumIntro l) les) = do
  let (ls, _) = unzip les
  CaseValue l `elem` ls || CaseDefault `elem` ls
isReduciblePreTerm (m, PreTermEnumElim e les) =
  isReduciblePreMeta m ||
  isReduciblePreTerm e || any isReduciblePreTerm (map snd les)
isReduciblePreTerm (m, PreTermArray _ dom cod) =
  isReduciblePreMeta m || isReduciblePreTerm dom || isReduciblePreTerm cod
isReduciblePreTerm (m, PreTermArrayIntro _ les) =
  isReduciblePreMeta m || any isReduciblePreTerm (map snd les)
isReduciblePreTerm (_, PreTermArrayElim _ (_, PreTermArrayIntro _ les) (_, PreTermEnumIntro l))
  | l `elem` map fst les = True
isReduciblePreTerm (m, PreTermArrayElim _ e1 e2) =
  isReduciblePreMeta m || isReduciblePreTerm e1 || isReduciblePreTerm e2

isReduciblePreMeta :: PreMeta -> Bool
isReduciblePreMeta (PreMetaNonTerminal t _) = isReduciblePreTerm t
isReduciblePreMeta _ = False

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
