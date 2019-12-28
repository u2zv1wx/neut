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
  | PreTermArray ArrayKind PreTermPlus
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

varPreTermPlus :: PreTermPlus -> [Identifier]
varPreTermPlus (_, PreTermTau) = []
varPreTermPlus (_, PreTermTheta _) = []
varPreTermPlus (_, PreTermUpsilon x) = [x]
varPreTermPlus (_, PreTermPi xts t) = do
  varPreTermPlusBindings xts [t]
varPreTermPlus (_, PreTermPiIntro xts e) = do
  varPreTermPlusBindings xts [e]
varPreTermPlus (_, PreTermPiElim e es) = do
  let xhs = varPreTermPlus e
  let yhs = concatMap varPreTermPlus es
  xhs ++ yhs
varPreTermPlus (_, PreTermMu ut e) = do
  varPreTermPlusBindings [ut] [e]
varPreTermPlus (_, PreTermZeta _) = []
varPreTermPlus (_, PreTermIntS _ _) = []
varPreTermPlus (_, PreTermIntU _ _) = []
varPreTermPlus (_, PreTermInt _) = []
varPreTermPlus (_, PreTermFloat16 _) = []
varPreTermPlus (_, PreTermFloat32 _) = []
varPreTermPlus (_, PreTermFloat64 _) = []
varPreTermPlus (_, PreTermFloat _) = []
varPreTermPlus (_, PreTermEnum _) = []
varPreTermPlus (_, PreTermEnumIntro _) = []
varPreTermPlus (_, PreTermEnumElim e les) = do
  let xhs = varPreTermPlus e
  let yhs = concatMap (\(_, body) -> varPreTermPlus body) les
  xhs ++ yhs
varPreTermPlus (_, PreTermArray _ t) = do
  varPreTermPlus t
varPreTermPlus (_, PreTermArrayIntro _ les) = do
  concatMap (\(_, body) -> varPreTermPlus body) les
varPreTermPlus (_, PreTermArrayElim _ e1 e2) = do
  varPreTermPlus e1 ++ varPreTermPlus e2

varPreTermPlusBindings :: [IdentifierPlus] -> [PreTermPlus] -> [Hole]
varPreTermPlusBindings [] es = do
  concatMap varPreTermPlus es
varPreTermPlusBindings ((x, t):xts) es = do
  let hs1 = varPreTermPlus t
  let hs2 = varPreTermPlusBindings xts es
  hs1 ++ filter (/= x) hs2

holePreTermPlus :: PreTermPlus -> [Hole]
holePreTermPlus (_, PreTermTau) = []
holePreTermPlus (_, PreTermTheta _) = []
holePreTermPlus (_, PreTermUpsilon _) = []
holePreTermPlus (_, PreTermPi xts t) = do
  holePreTermPlusBindings xts [t]
holePreTermPlus (_, PreTermPiIntro xts e) = do
  holePreTermPlusBindings xts [e]
holePreTermPlus (_, PreTermPiElim e es) = do
  holePreTermPlus e ++ concatMap holePreTermPlus es
holePreTermPlus (_, PreTermMu ut e) = do
  holePreTermPlusBindings [ut] [e]
holePreTermPlus (_, PreTermZeta h) = [h]
holePreTermPlus (_, PreTermIntS _ _) = []
holePreTermPlus (_, PreTermIntU _ _) = []
holePreTermPlus (_, PreTermInt _) = []
holePreTermPlus (_, PreTermFloat16 _) = []
holePreTermPlus (_, PreTermFloat32 _) = []
holePreTermPlus (_, PreTermFloat64 _) = []
holePreTermPlus (_, PreTermFloat _) = []
holePreTermPlus (_, PreTermEnum _) = []
holePreTermPlus (_, PreTermEnumIntro _) = []
holePreTermPlus (_, PreTermEnumElim e les) = do
  let xhs = holePreTermPlus e
  let yhs = concatMap (\(_, body) -> holePreTermPlus body) les
  xhs ++ yhs
holePreTermPlus (_, PreTermArray _ e) = holePreTermPlus e
holePreTermPlus (_, PreTermArrayIntro _ les) = do
  concatMap (\(_, body) -> holePreTermPlus body) les
holePreTermPlus (_, PreTermArrayElim _ e1 e2) = do
  holePreTermPlus e1 ++ holePreTermPlus e2

holePreTermPlusBindings :: [IdentifierPlus] -> [PreTermPlus] -> [Hole]
holePreTermPlusBindings [] es = do
  concatMap holePreTermPlus es
holePreTermPlusBindings ((_, t):xts) es = do
  holePreTermPlus t ++ holePreTermPlusBindings xts es

-- substPreTermPlus :: SubstPreTerm -> PreTermPlus -> PreTermPlus
-- substPreTermPlus _ (m, PreTermTau) = do
--   (m, PreTermTau)
-- substPreTermPlus _ (m, PreTermTheta t) = do
--   (m, PreTermTheta t)
-- substPreTermPlus sub (m, PreTermUpsilon x) = do
--   fromMaybe (m, PreTermUpsilon x) (lookup x sub)
-- substPreTermPlus sub (m, PreTermPi xts t) = do
--   let (xts', t') = substPreTermPlusBindingsWithBody sub xts t
--   (m, PreTermPi xts' t')
-- substPreTermPlus sub (m, PreTermPiIntro xts body) = do
--   let (xts', body') = substPreTermPlusBindingsWithBody sub xts body
--   (m, PreTermPiIntro xts' body')
-- substPreTermPlus sub (m, PreTermPiElim e es) = do
--   let e' = substPreTermPlus sub e
--   let es' = map (substPreTermPlus sub) es
--   (m, PreTermPiElim e' es')
-- substPreTermPlus sub (m, PreTermMu (x, t) e) = do
--   let t' = substPreTermPlus sub t
--   let e' = substPreTermPlus (filter (\(k, _) -> k /= x) sub) e
--   (m, PreTermMu (x, t') e')
-- substPreTermPlus sub (m, PreTermZeta s) = do
--   fromMaybe (m, PreTermZeta s) (lookup s sub)
-- substPreTermPlus _ (m, PreTermIntS size x) = do
--   (m, PreTermIntS size x)
-- substPreTermPlus _ (m, PreTermIntU size x) = do
--   (m, PreTermIntU size x)
-- substPreTermPlus _ (m, PreTermInt x) = do
--   (m, PreTermInt x)
-- substPreTermPlus _ (m, PreTermFloat16 x) = do
--   (m, PreTermFloat16 x)
-- substPreTermPlus _ (m, PreTermFloat32 x) = do
--   (m, PreTermFloat32 x)
-- substPreTermPlus _ (m, PreTermFloat64 x) = do
--   (m, PreTermFloat64 x)
-- substPreTermPlus _ (m, PreTermFloat x) = do
--   (m, PreTermFloat x)
-- substPreTermPlus _ (m, PreTermEnum x) = do
--   (m, PreTermEnum x)
-- substPreTermPlus _ (m, PreTermEnumIntro l) = do
--   (m, PreTermEnumIntro l)
-- substPreTermPlus sub (m, PreTermEnumElim e branchList) = do
--   let e' = substPreTermPlus sub e
--   let (caseList, es) = unzip branchList
--   let es' = map (substPreTermPlus sub) es
--   (m, PreTermEnumElim e' (zip caseList es'))
-- substPreTermPlus sub (m, PreTermArray kind indexType) = do
--   let indexType' = substPreTermPlus sub indexType
--   (m, PreTermArray kind indexType')
-- substPreTermPlus sub (m, PreTermArrayIntro kind les) = do
--   let (ls, es) = unzip les
--   let es' = map (substPreTermPlus sub) es
--   (m, PreTermArrayIntro kind (zip ls es'))
-- substPreTermPlus sub (m, PreTermArrayElim kind e1 e2) = do
--   let e1' = substPreTermPlus sub e1
--   let e2' = substPreTermPlus sub e2
--   (m, PreTermArrayElim kind e1' e2')
-- substPreTermPlusBindingsWithBody ::
--      SubstPreTerm
--   -> [IdentifierPlus]
--   -> PreTermPlus
--   -> ([IdentifierPlus], PreTermPlus)
-- substPreTermPlusBindingsWithBody sub [] e = do
--   let e' = substPreTermPlus sub e
--   ([], e')
-- substPreTermPlusBindingsWithBody sub ((x, t):xts) e = do
--   let sub' = filter (\(k, _) -> k /= x) sub
--   let (xts', e') = substPreTermPlusBindingsWithBody sub' xts e
--   let t' = substPreTermPlus sub t
--   ((x, t') : xts', e')
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
substPreTermPlus sub (m, PreTermArray kind indexType) = do
  let m' = substPreMeta sub m
  let indexType' = substPreTermPlus sub indexType
  (m', PreTermArray kind indexType')
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
isReduciblePreTerm (_, PreTermTau) = False
isReduciblePreTerm (_, PreTermTheta _) = False
isReduciblePreTerm (_, PreTermUpsilon _) = False
isReduciblePreTerm (_, PreTermPi xts cod) =
  any isReduciblePreTerm (map snd xts) || isReduciblePreTerm cod
isReduciblePreTerm (_, PreTermPiIntro xts e) =
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
isReduciblePreTerm (_, PreTermPiElim e es) =
  isReduciblePreTerm e || any isReduciblePreTerm es
isReduciblePreTerm (_, PreTermMu (_, t) e) =
  isReduciblePreTerm t || isReduciblePreTerm e
isReduciblePreTerm (_, PreTermZeta _) = False
isReduciblePreTerm (_, PreTermIntS _ _) = False
isReduciblePreTerm (_, PreTermIntU _ _) = False
isReduciblePreTerm (_, PreTermInt _) = False
isReduciblePreTerm (_, PreTermFloat16 _) = False
isReduciblePreTerm (_, PreTermFloat32 _) = False
isReduciblePreTerm (_, PreTermFloat64 _) = False
isReduciblePreTerm (_, PreTermFloat _) = False
isReduciblePreTerm (_, PreTermEnum _) = False
isReduciblePreTerm (_, PreTermEnumIntro _) = False
isReduciblePreTerm (_, PreTermEnumElim (_, PreTermEnumIntro l) les) = do
  let (ls, _) = unzip les
  CaseValue l `elem` ls || CaseDefault `elem` ls
isReduciblePreTerm (_, PreTermEnumElim e les) =
  isReduciblePreTerm e || any isReduciblePreTerm (map snd les)
isReduciblePreTerm (_, PreTermArray _ indexType) = isReduciblePreTerm indexType
isReduciblePreTerm (_, PreTermArrayIntro _ les) =
  any isReduciblePreTerm (map snd les)
isReduciblePreTerm (_, PreTermArrayElim _ (_, PreTermArrayIntro _ les) (_, PreTermEnumIntro l))
  | l `elem` map fst les = True
isReduciblePreTerm (_, PreTermArrayElim _ e1 e2) =
  isReduciblePreTerm e1 || isReduciblePreTerm e2

-- valueの定義がおかしい？
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
