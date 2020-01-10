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
  | WeakTermIter IdentifierPlus [IdentifierPlus] WeakTermPlus -- CBN recursion ~ CBV iteration
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
  deriving (Show, Eq)

type WeakTermPlus = (PreMeta, WeakTerm)

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTermPlus)

data PreMeta
  = PreMetaTerminal Meta
  | PreMetaNonTerminal WeakTermPlus Meta

instance Show PreMeta where
  show _ = "_"

instance Eq PreMeta where
  _ == _ = True

varWeakTermPlus :: WeakTermPlus -> [Identifier]
varWeakTermPlus (m, WeakTermTau) = varPreMeta m
varWeakTermPlus (m, WeakTermUpsilon x) = x : varPreMeta m
varWeakTermPlus (m, WeakTermPi xts t) = do
  varPreMeta m ++ varWeakTermPlusBindings xts [t]
varWeakTermPlus (m, WeakTermPiIntro xts e) = do
  varPreMeta m ++ varWeakTermPlusBindings xts [e]
varWeakTermPlus (m, WeakTermPiElim e es) = do
  let xhs = varWeakTermPlus e
  let yhs = concatMap varWeakTermPlus es
  varPreMeta m ++ xhs ++ yhs
varWeakTermPlus (m, WeakTermIter (x, t) xts e) = do
  varPreMeta m ++
    varWeakTermPlus t ++ filter (/= x) (varWeakTermPlusBindings xts [e])
varWeakTermPlus (m, WeakTermConst _) = varPreMeta m
varWeakTermPlus (m, WeakTermConstDecl xt e) =
  varPreMeta m ++ varWeakTermPlusBindings [xt] [e]
varWeakTermPlus (m, WeakTermZeta _) = varPreMeta m
varWeakTermPlus (m, WeakTermIntS _ _) = varPreMeta m
varWeakTermPlus (m, WeakTermIntU _ _) = varPreMeta m
varWeakTermPlus (m, WeakTermInt _) = varPreMeta m
varWeakTermPlus (m, WeakTermFloat16 _) = varPreMeta m
varWeakTermPlus (m, WeakTermFloat32 _) = varPreMeta m
varWeakTermPlus (m, WeakTermFloat64 _) = varPreMeta m
varWeakTermPlus (m, WeakTermFloat _) = varPreMeta m
varWeakTermPlus (m, WeakTermEnum _) = varPreMeta m
varWeakTermPlus (m, WeakTermEnumIntro _) = varPreMeta m
varWeakTermPlus (m, WeakTermEnumElim e les) = do
  let xhs = varWeakTermPlus e
  let yhs = concatMap (varWeakTermPlus . snd) les
  varPreMeta m ++ xhs ++ yhs
varWeakTermPlus (m, WeakTermArray _ t) = do
  varPreMeta m ++ varWeakTermPlus t
varWeakTermPlus (m, WeakTermArrayIntro _ les) = do
  varPreMeta m ++ concatMap (\(_, body) -> varWeakTermPlus body) les
varWeakTermPlus (m, WeakTermArrayElim _ e1 e2) = do
  varPreMeta m ++ varWeakTermPlus e1 ++ varWeakTermPlus e2

varWeakTermPlusBindings :: [IdentifierPlus] -> [WeakTermPlus] -> [Hole]
varWeakTermPlusBindings [] es = do
  concatMap varWeakTermPlus es
varWeakTermPlusBindings ((x, t):xts) es = do
  let hs1 = varWeakTermPlus t
  let hs2 = varWeakTermPlusBindings xts es
  hs1 ++ filter (/= x) hs2

varPreMeta :: PreMeta -> [Hole]
varPreMeta _ = []

-- varPreMeta (PreMetaTerminal _) = []
-- varPreMeta (PreMetaNonTerminal t _) = varWeakTermPlus t
holeWeakTermPlus :: WeakTermPlus -> [Hole]
holeWeakTermPlus (m, WeakTermTau) = holePreMeta m
holeWeakTermPlus (m, WeakTermUpsilon _) = holePreMeta m
holeWeakTermPlus (m, WeakTermPi xts t) =
  holePreMeta m ++ holeWeakTermPlusBindings xts [t]
holeWeakTermPlus (m, WeakTermPiIntro xts e) =
  holePreMeta m ++ holeWeakTermPlusBindings xts [e]
holeWeakTermPlus (m, WeakTermPiElim e es) =
  holePreMeta m ++ holeWeakTermPlus e ++ concatMap holeWeakTermPlus es
holeWeakTermPlus (m, WeakTermIter (_, t) xts e) =
  holePreMeta m ++ holeWeakTermPlus t ++ holeWeakTermPlusBindings xts [e]
holeWeakTermPlus (m, WeakTermZeta h) = h : holePreMeta m
holeWeakTermPlus (m, WeakTermConst _) = holePreMeta m
holeWeakTermPlus (m, WeakTermConstDecl xt e) =
  holePreMeta m ++ holeWeakTermPlusBindings [xt] [e]
holeWeakTermPlus (m, WeakTermIntS _ _) = holePreMeta m
holeWeakTermPlus (m, WeakTermIntU _ _) = holePreMeta m
holeWeakTermPlus (m, WeakTermInt _) = holePreMeta m
holeWeakTermPlus (m, WeakTermFloat16 _) = holePreMeta m
holeWeakTermPlus (m, WeakTermFloat32 _) = holePreMeta m
holeWeakTermPlus (m, WeakTermFloat64 _) = holePreMeta m
holeWeakTermPlus (m, WeakTermFloat _) = holePreMeta m
holeWeakTermPlus (m, WeakTermEnum _) = holePreMeta m
holeWeakTermPlus (m, WeakTermEnumIntro _) = holePreMeta m
holeWeakTermPlus (m, WeakTermEnumElim e les) = do
  let xhs = holeWeakTermPlus e
  let yhs = concatMap (\(_, body) -> holeWeakTermPlus body) les
  holePreMeta m ++ xhs ++ yhs
holeWeakTermPlus (m, WeakTermArray _ e) = holePreMeta m ++ holeWeakTermPlus e
holeWeakTermPlus (m, WeakTermArrayIntro _ les) = do
  holePreMeta m ++ concatMap (\(_, body) -> holeWeakTermPlus body) les
holeWeakTermPlus (m, WeakTermArrayElim _ e1 e2) = do
  holePreMeta m ++ holeWeakTermPlus e1 ++ holeWeakTermPlus e2

holeWeakTermPlusBindings :: [IdentifierPlus] -> [WeakTermPlus] -> [Hole]
holeWeakTermPlusBindings [] es = do
  concatMap holeWeakTermPlus es
holeWeakTermPlusBindings ((_, t):xts) es = do
  holeWeakTermPlus t ++ holeWeakTermPlusBindings xts es

holePreMeta :: PreMeta -> [Hole]
holePreMeta _ = []

-- holePreMeta (PreMetaTerminal _) = []
-- holePreMeta (PreMetaNonTerminal t _) = holeWeakTermPlus t
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
substWeakTermPlus sub (m, WeakTermIter (x, t) xts e) = do
  let m' = substPreMeta sub m
  let t' = substWeakTermPlus sub t
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermPlusBindingsWithBody sub' xts e
  (m', WeakTermIter (x, t') xts' e')
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
substPreMeta _ m = m

-- substPreMeta _ m@(PreMetaTerminal _) = m
-- substPreMeta sub (PreMetaNonTerminal t ml) =
--   PreMetaNonTerminal (substWeakTermPlus sub t) ml
typeOf :: WeakTermPlus -> WeakTermPlus
typeOf (m, _) = typeOf' m

typeOf' :: PreMeta -> WeakTermPlus
typeOf' (PreMetaTerminal _) = univ
typeOf' (PreMetaNonTerminal t _) = t

univ :: WeakTermPlus
univ = (PreMetaTerminal emptyMeta, WeakTermTau)
