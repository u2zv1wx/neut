module Data.WeakTerm where

import Data.Maybe (fromMaybe)
import Numeric.Half

import Data.Basic

data WeakTerm
  = WeakTermTau
  | WeakTermUpsilon Identifier
  | WeakTermPi [IdentifierPlus] WeakTermPlus
  | WeakTermPiIntro [IdentifierPlus] WeakTermPlus
  | WeakTermPiElim WeakTermPlus [WeakTermPlus]
  | WeakTermMu IdentifierPlus WeakTermPlus
  | WeakTermZeta Identifier
  | WeakTermConst Identifier
  | WeakTermConstDecl IdentifierPlus WeakTermPlus
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
  | WeakTermArray ArrayKind WeakTermPlus
  | WeakTermArrayIntro ArrayKind [(EnumValue, WeakTermPlus)]
  | WeakTermArrayElim ArrayKind WeakTermPlus WeakTermPlus
  deriving (Show)

type WeakTermPlus = (PreMeta, WeakTerm)

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTermPlus)

data PreMeta
  = PreMetaTerminal (Maybe Loc)
  | PreMetaNonTerminal WeakTermPlus (Maybe Loc)
  -- deriving (Show)

instance Show PreMeta where
  show _ = "_"

varWeakTermPlus :: WeakTermPlus -> [Identifier]
varWeakTermPlus (_, WeakTermTau) = []
varWeakTermPlus (_, WeakTermUpsilon x) = [x]
varWeakTermPlus (_, WeakTermPi xts t) = do
  varWeakTermPlusBindings xts [t]
varWeakTermPlus (_, WeakTermPiIntro xts e) = do
  varWeakTermPlusBindings xts [e]
varWeakTermPlus (_, WeakTermPiElim e es) = do
  let xhs = varWeakTermPlus e
  let yhs = concatMap varWeakTermPlus es
  xhs ++ yhs
varWeakTermPlus (_, WeakTermMu ut e) = do
  varWeakTermPlusBindings [ut] [e]
varWeakTermPlus (_, WeakTermConst _) = []
varWeakTermPlus (_, WeakTermConstDecl xt e) = varWeakTermPlusBindings [xt] [e]
varWeakTermPlus (_, WeakTermZeta _) = []
varWeakTermPlus (_, WeakTermIntS _ _) = []
varWeakTermPlus (_, WeakTermIntU _ _) = []
varWeakTermPlus (_, WeakTermInt _) = []
varWeakTermPlus (_, WeakTermFloat16 _) = []
varWeakTermPlus (_, WeakTermFloat32 _) = []
varWeakTermPlus (_, WeakTermFloat64 _) = []
varWeakTermPlus (_, WeakTermFloat _) = []
varWeakTermPlus (_, WeakTermEnum _) = []
varWeakTermPlus (_, WeakTermEnumIntro _) = []
varWeakTermPlus (_, WeakTermEnumElim e les) = do
  let xhs = varWeakTermPlus e
  let yhs = concatMap (\(_, body) -> varWeakTermPlus body) les
  xhs ++ yhs
varWeakTermPlus (_, WeakTermArray _ t) = do
  varWeakTermPlus t
varWeakTermPlus (_, WeakTermArrayIntro _ les) = do
  concatMap (\(_, body) -> varWeakTermPlus body) les
varWeakTermPlus (_, WeakTermArrayElim _ e1 e2) = do
  varWeakTermPlus e1 ++ varWeakTermPlus e2

varWeakTermPlusBindings :: [IdentifierPlus] -> [WeakTermPlus] -> [Hole]
varWeakTermPlusBindings [] es = do
  concatMap varWeakTermPlus es
varWeakTermPlusBindings ((x, t):xts) es = do
  let hs1 = varWeakTermPlus t
  let hs2 = varWeakTermPlusBindings xts es
  hs1 ++ filter (/= x) hs2

holeWeakTermPlus :: WeakTermPlus -> [Hole]
holeWeakTermPlus (_, WeakTermTau) = []
holeWeakTermPlus (_, WeakTermUpsilon _) = []
holeWeakTermPlus (_, WeakTermPi xts t) = holeWeakTermPlusBindings xts [t]
holeWeakTermPlus (_, WeakTermPiIntro xts e) = holeWeakTermPlusBindings xts [e]
holeWeakTermPlus (_, WeakTermPiElim e es) =
  holeWeakTermPlus e ++ concatMap holeWeakTermPlus es
holeWeakTermPlus (_, WeakTermMu ut e) = holeWeakTermPlusBindings [ut] [e]
holeWeakTermPlus (_, WeakTermZeta h) = [h]
holeWeakTermPlus (_, WeakTermConst _) = []
holeWeakTermPlus (_, WeakTermConstDecl xt e) = holeWeakTermPlusBindings [xt] [e]
holeWeakTermPlus (_, WeakTermIntS _ _) = []
holeWeakTermPlus (_, WeakTermIntU _ _) = []
holeWeakTermPlus (_, WeakTermInt _) = []
holeWeakTermPlus (_, WeakTermFloat16 _) = []
holeWeakTermPlus (_, WeakTermFloat32 _) = []
holeWeakTermPlus (_, WeakTermFloat64 _) = []
holeWeakTermPlus (_, WeakTermFloat _) = []
holeWeakTermPlus (_, WeakTermEnum _) = []
holeWeakTermPlus (_, WeakTermEnumIntro _) = []
holeWeakTermPlus (_, WeakTermEnumElim e les) = do
  let xhs = holeWeakTermPlus e
  let yhs = concatMap (\(_, body) -> holeWeakTermPlus body) les
  xhs ++ yhs
holeWeakTermPlus (_, WeakTermArray _ e) = holeWeakTermPlus e
holeWeakTermPlus (_, WeakTermArrayIntro _ les) = do
  concatMap (\(_, body) -> holeWeakTermPlus body) les
holeWeakTermPlus (_, WeakTermArrayElim _ e1 e2) = do
  holeWeakTermPlus e1 ++ holeWeakTermPlus e2

holeWeakTermPlusBindings :: [IdentifierPlus] -> [WeakTermPlus] -> [Hole]
holeWeakTermPlusBindings [] es = do
  concatMap holeWeakTermPlus es
holeWeakTermPlusBindings ((_, t):xts) es = do
  holeWeakTermPlus t ++ holeWeakTermPlusBindings xts es

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WeakTermPlus
substWeakTermPlus sub (m, WeakTermTau) = do
  let m' = substPreMeta sub m
  (m', WeakTermTau)
substWeakTermPlus sub (m, WeakTermUpsilon x) = do
  let m' = substPreMeta sub m
  fromMaybe (m', WeakTermUpsilon x) (lookup x sub)
substWeakTermPlus sub (m, WeakTermPi xts t) = do
  let m' = substPreMeta sub m
  let (xts', t') = substWeakTermPlusBindingsWithBody sub xts t
  (m', WeakTermPi xts' t')
substWeakTermPlus sub (m, WeakTermPiIntro xts body) = do
  let m' = substPreMeta sub m
  let (xts', body') = substWeakTermPlusBindingsWithBody sub xts body
  (m', WeakTermPiIntro xts' body')
substWeakTermPlus sub (m, WeakTermPiElim e es) = do
  let m' = substPreMeta sub m
  let e' = substWeakTermPlus sub e
  let es' = map (substWeakTermPlus sub) es
  (m', WeakTermPiElim e' es')
substWeakTermPlus sub (m, WeakTermMu (x, t) e) = do
  let m' = substPreMeta sub m
  let t' = substWeakTermPlus sub t
  let e' = substWeakTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m', WeakTermMu (x, t') e')
substWeakTermPlus sub (m, WeakTermConst x) = do
  let m' = substPreMeta sub m
  (m', WeakTermConst x)
substWeakTermPlus sub (m, WeakTermConstDecl (x, t) e) = do
  let m' = substPreMeta sub m
  let t' = substWeakTermPlus sub t
  let e' = substWeakTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m', WeakTermConstDecl (x, t') e')
substWeakTermPlus sub (m, WeakTermZeta s) = do
  let m' = substPreMeta sub m
  fromMaybe (m', WeakTermZeta s) (lookup s sub)
substWeakTermPlus sub (m, WeakTermIntS size x) = do
  let m' = substPreMeta sub m
  (m', WeakTermIntS size x)
substWeakTermPlus sub (m, WeakTermIntU size x) = do
  let m' = substPreMeta sub m
  (m', WeakTermIntU size x)
substWeakTermPlus sub (m, WeakTermInt x) = do
  let m' = substPreMeta sub m
  (m', WeakTermInt x)
substWeakTermPlus sub (m, WeakTermFloat16 x) = do
  let m' = substPreMeta sub m
  (m', WeakTermFloat16 x)
substWeakTermPlus sub (m, WeakTermFloat32 x) = do
  let m' = substPreMeta sub m
  (m', WeakTermFloat32 x)
substWeakTermPlus sub (m, WeakTermFloat64 x) = do
  let m' = substPreMeta sub m
  (m', WeakTermFloat64 x)
substWeakTermPlus sub (m, WeakTermFloat x) = do
  let m' = substPreMeta sub m
  (m', WeakTermFloat x)
substWeakTermPlus sub (m, WeakTermEnum x) = do
  let m' = substPreMeta sub m
  (m', WeakTermEnum x)
substWeakTermPlus sub (m, WeakTermEnumIntro l) = do
  let m' = substPreMeta sub m
  (m', WeakTermEnumIntro l)
substWeakTermPlus sub (m, WeakTermEnumElim e branchList) = do
  let m' = substPreMeta sub m
  let e' = substWeakTermPlus sub e
  let (caseList, es) = unzip branchList
  let es' = map (substWeakTermPlus sub) es
  (m', WeakTermEnumElim e' (zip caseList es'))
substWeakTermPlus sub (m, WeakTermArray kind indexType) = do
  let m' = substPreMeta sub m
  let indexType' = substWeakTermPlus sub indexType
  (m', WeakTermArray kind indexType')
substWeakTermPlus sub (m, WeakTermArrayIntro kind les) = do
  let m' = substPreMeta sub m
  let (ls, es) = unzip les
  let es' = map (substWeakTermPlus sub) es
  (m', WeakTermArrayIntro kind (zip ls es'))
substWeakTermPlus sub (m, WeakTermArrayElim kind e1 e2) = do
  let m' = substPreMeta sub m
  let e1' = substWeakTermPlus sub e1
  let e2' = substWeakTermPlus sub e2
  (m', WeakTermArrayElim kind e1' e2')

substWeakTermPlusBindingsWithBody ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> ([IdentifierPlus], WeakTermPlus)
substWeakTermPlusBindingsWithBody sub [] e = do
  let e' = substWeakTermPlus sub e
  ([], e')
substWeakTermPlusBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermPlusBindingsWithBody sub' xts e
  let t' = substWeakTermPlus sub t
  ((x, t') : xts', e')

substPreMeta :: SubstWeakTerm -> PreMeta -> PreMeta
substPreMeta _ m@(PreMetaTerminal _) = m
substPreMeta sub (PreMetaNonTerminal t ml) =
  PreMetaNonTerminal (substWeakTermPlus sub t) ml

isReducibleWeakTerm :: WeakTermPlus -> Bool
isReducibleWeakTerm (_, WeakTermTau) = False
isReducibleWeakTerm (_, WeakTermUpsilon _) = False
isReducibleWeakTerm (_, WeakTermPi xts cod) =
  any isReducibleWeakTerm (map snd xts) || isReducibleWeakTerm cod
isReducibleWeakTerm (_, WeakTermPiIntro xts e) =
  any isReducibleWeakTerm (map snd xts) || isReducibleWeakTerm e
isReducibleWeakTerm (_, WeakTermPiElim (_, WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducibleWeakTerm (_, WeakTermPiElim (_, WeakTermMu _ _) es) = all isValue es -- muのときだけCBV的な挙動を要求する
isReducibleWeakTerm (_, WeakTermPiElim (_, WeakTermUpsilon c) [(_, WeakTermIntS _ _), (_, WeakTermIntS _ _)])
  | Just (LowTypeIntS _, _) <- asBinaryOpMaybe c = True
isReducibleWeakTerm (_, WeakTermPiElim (_, WeakTermUpsilon c) [(_, WeakTermIntU _ _), (_, WeakTermIntU _ _)])
  | Just (LowTypeIntU _, _) <- asBinaryOpMaybe c = True
isReducibleWeakTerm (_, WeakTermPiElim (_, WeakTermUpsilon c) [(_, WeakTermFloat16 _), (_, WeakTermFloat16 _)])
  | Just (LowTypeFloat FloatSize16, _) <- asBinaryOpMaybe c = True
isReducibleWeakTerm (_, WeakTermPiElim (_, WeakTermUpsilon c) [(_, WeakTermFloat32 _), (_, WeakTermFloat32 _)])
  | Just (LowTypeFloat FloatSize32, _) <- asBinaryOpMaybe c = True
isReducibleWeakTerm (_, WeakTermPiElim (_, WeakTermUpsilon c) [(_, WeakTermFloat64 _), (_, WeakTermFloat64 _)])
  | Just (LowTypeFloat FloatSize64, _) <- asBinaryOpMaybe c = True
isReducibleWeakTerm (_, WeakTermPiElim e es) =
  isReducibleWeakTerm e || any isReducibleWeakTerm es
isReducibleWeakTerm (_, WeakTermMu (_, t) e) =
  isReducibleWeakTerm t || isReducibleWeakTerm e
isReducibleWeakTerm (_, WeakTermConst _) = False
isReducibleWeakTerm (_, WeakTermConstDecl (_, t) e) =
  isReducibleWeakTerm t || isReducibleWeakTerm e
isReducibleWeakTerm (_, WeakTermZeta _) = False
isReducibleWeakTerm (_, WeakTermIntS _ _) = False
isReducibleWeakTerm (_, WeakTermIntU _ _) = False
isReducibleWeakTerm (_, WeakTermInt _) = False
isReducibleWeakTerm (_, WeakTermFloat16 _) = False
isReducibleWeakTerm (_, WeakTermFloat32 _) = False
isReducibleWeakTerm (_, WeakTermFloat64 _) = False
isReducibleWeakTerm (_, WeakTermFloat _) = False
isReducibleWeakTerm (_, WeakTermEnum _) = False
isReducibleWeakTerm (_, WeakTermEnumIntro _) = False
isReducibleWeakTerm (_, WeakTermEnumElim (_, WeakTermEnumIntro l) les) = do
  let (ls, _) = unzip les
  CaseValue l `elem` ls || CaseDefault `elem` ls
isReducibleWeakTerm (_, WeakTermEnumElim e les) =
  isReducibleWeakTerm e || any isReducibleWeakTerm (map snd les)
isReducibleWeakTerm (_, WeakTermArray _ indexType) =
  isReducibleWeakTerm indexType
isReducibleWeakTerm (_, WeakTermArrayIntro _ les) =
  any isReducibleWeakTerm (map snd les)
isReducibleWeakTerm (_, WeakTermArrayElim _ (_, WeakTermArrayIntro _ les) (_, WeakTermEnumIntro l))
  | l `elem` map fst les = True
isReducibleWeakTerm (_, WeakTermArrayElim _ e1 e2) =
  isReducibleWeakTerm e1 || isReducibleWeakTerm e2

isValue :: WeakTermPlus -> Bool
isValue (_, WeakTermTau) = True
isValue (_, WeakTermUpsilon _) = True
isValue (_, WeakTermPi {}) = True
isValue (_, WeakTermPiIntro {}) = True
isValue (_, WeakTermConst _) = True
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

typeOf :: WeakTermPlus -> WeakTermPlus
typeOf (m, _) = typeOf' m

typeOf' :: PreMeta -> WeakTermPlus
typeOf' (PreMetaTerminal _) = univ
typeOf' (PreMetaNonTerminal t _) = t

univ :: WeakTermPlus
univ = (PreMetaTerminal Nothing, WeakTermTau)
