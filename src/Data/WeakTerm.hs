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

type WeakTermPlus = (Meta, WeakTerm)

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTermPlus)

varWeakTermPlus :: WeakTermPlus -> [Identifier]
varWeakTermPlus (_, WeakTermTau) = []
varWeakTermPlus (_, WeakTermUpsilon x) = x : []
varWeakTermPlus (_, WeakTermPi xts t) = do
  varWeakTermPlusBindings xts [t]
varWeakTermPlus (_, WeakTermPiIntro xts e) = do
  varWeakTermPlusBindings xts [e]
varWeakTermPlus (_, WeakTermPiElim e es) = do
  let xhs = varWeakTermPlus e
  let yhs = concatMap varWeakTermPlus es
  xhs ++ yhs
varWeakTermPlus (_, WeakTermIter (x, t) xts e) = do
  varWeakTermPlus t ++ filter (/= x) (varWeakTermPlusBindings xts [e])
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
  let yhs = concatMap (varWeakTermPlus . snd) les
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
holeWeakTermPlus (_, WeakTermIter (_, t) xts e) =
  holeWeakTermPlus t ++ holeWeakTermPlusBindings xts [e]
holeWeakTermPlus (_, WeakTermZeta h) = h : []
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
substWeakTermPlus _ (m, WeakTermTau) = do
  (m, WeakTermTau)
substWeakTermPlus sub (m, WeakTermUpsilon x) = do
  fromMaybe (m, WeakTermUpsilon x) (lookup x sub)
substWeakTermPlus sub (m, WeakTermPi xts t) = do
  let (xts', t') = substWeakTermPlusBindingsWithBody sub xts t
  (m, WeakTermPi xts' t')
substWeakTermPlus sub (m, WeakTermPiIntro xts body) = do
  let (xts', body') = substWeakTermPlusBindingsWithBody sub xts body
  (m, WeakTermPiIntro xts' body')
substWeakTermPlus sub (m, WeakTermPiElim e es) = do
  let e' = substWeakTermPlus sub e
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermPiElim e' es')
substWeakTermPlus sub (m, WeakTermIter (x, t) xts e) = do
  let t' = substWeakTermPlus sub t
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermPlusBindingsWithBody sub' xts e
  (m, WeakTermIter (x, t') xts' e')
substWeakTermPlus _ (m, WeakTermConst x) = do
  (m, WeakTermConst x)
substWeakTermPlus sub (m, WeakTermConstDecl (x, t) e) = do
  let t' = substWeakTermPlus sub t
  let e' = substWeakTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m, WeakTermConstDecl (x, t') e')
substWeakTermPlus sub (m, WeakTermZeta s) = do
  fromMaybe (m, WeakTermZeta s) (lookup s sub)
substWeakTermPlus _ (m, WeakTermIntS size x) = do
  (m, WeakTermIntS size x)
substWeakTermPlus _ (m, WeakTermIntU size x) = do
  (m, WeakTermIntU size x)
substWeakTermPlus _ (m, WeakTermInt x) = do
  (m, WeakTermInt x)
substWeakTermPlus _ (m, WeakTermFloat16 x) = do
  (m, WeakTermFloat16 x)
substWeakTermPlus _ (m, WeakTermFloat32 x) = do
  (m, WeakTermFloat32 x)
substWeakTermPlus _ (m, WeakTermFloat64 x) = do
  (m, WeakTermFloat64 x)
substWeakTermPlus _ (m, WeakTermFloat x) = do
  (m, WeakTermFloat x)
substWeakTermPlus _ (m, WeakTermEnum x) = do
  (m, WeakTermEnum x)
substWeakTermPlus _ (m, WeakTermEnumIntro l) = do
  (m, WeakTermEnumIntro l)
substWeakTermPlus sub (m, WeakTermEnumElim e branchList) = do
  let e' = substWeakTermPlus sub e
  let (caseList, es) = unzip branchList
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermEnumElim e' (zip caseList es'))
substWeakTermPlus sub (m, WeakTermArray kind indexType) = do
  let indexType' = substWeakTermPlus sub indexType
  (m, WeakTermArray kind indexType')
substWeakTermPlus sub (m, WeakTermArrayIntro kind les) = do
  let (ls, es) = unzip les
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermArrayIntro kind (zip ls es'))
substWeakTermPlus sub (m, WeakTermArrayElim kind e1 e2) = do
  let e1' = substWeakTermPlus sub e1
  let e2' = substWeakTermPlus sub e2
  (m, WeakTermArrayElim kind e1' e2')

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

univ :: WeakTermPlus
univ = (emptyMeta, WeakTermTau)
