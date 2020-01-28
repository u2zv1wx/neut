module Data.Term where

import Data.Maybe (fromMaybe)
import Numeric.Half

import Data.Basic

data Term
  = TermTau
  | TermUpsilon Identifier
  | TermPi [IdentifierPlus] TermPlus
  | TermPiIntro [IdentifierPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermIter IdentifierPlus [IdentifierPlus] TermPlus
  | TermConst Identifier
  | TermConstDecl IdentifierPlus TermPlus
  | TermFloat16 Half
  | TermFloat32 Float
  | TermFloat64 Double
  | TermEnum EnumType
  | TermEnumIntro EnumValue
  | TermEnumElim TermPlus [(Case, TermPlus)]
  | TermArray TermPlus ArrayKind -- array n3 u8 ~= n3 -> u8
  | TermArrayIntro ArrayKind [TermPlus]
  | TermArrayElim
      ArrayKind
      [IdentifierPlus] -- [(x1, return t1), ..., (xn, return tn)] with xi : ti
      TermPlus
      TermPlus
  | TermStruct [ArrayKind] -- e.g. (struct u8 u8 f16 f32 u64)
  | TermStructIntro [(TermPlus, ArrayKind)]
  | TermStructElim [(Meta, Identifier, ArrayKind)] TermPlus TermPlus
  deriving (Show)

type TermPlus = (Meta, Term)

type SubstTerm = [(Identifier, TermPlus)]

type Hole = Identifier

type IdentifierPlus = (Meta, Identifier, TermPlus)

toTermUpsilon :: Identifier -> TermPlus
toTermUpsilon x = do
  (emptyMeta, TermUpsilon x)

varTermPlus :: TermPlus -> [Identifier]
varTermPlus (_, TermTau) = []
varTermPlus (_, TermUpsilon x) = [x]
varTermPlus (_, TermPi xts t) = varTermPlus' xts [t]
varTermPlus (_, TermPiIntro xts e) = varTermPlus' xts [e]
varTermPlus (_, TermPiElim e es) = do
  let xs1 = varTermPlus e
  let xs2 = concatMap varTermPlus es
  xs1 ++ xs2
varTermPlus (_, TermIter (_, x, t) xts e) =
  varTermPlus t ++ filter (/= x) (varTermPlus' xts [e])
varTermPlus (_, TermConst _) = []
varTermPlus (_, TermConstDecl xt e) = varTermPlus' [xt] [e]
varTermPlus (_, TermFloat16 _) = []
varTermPlus (_, TermFloat32 _) = []
varTermPlus (_, TermFloat64 _) = []
varTermPlus (_, TermEnum _) = []
varTermPlus (_, TermEnumIntro _) = []
varTermPlus (_, TermEnumElim e les) = do
  let xs1 = varTermPlus e
  let es = map snd les
  let xs2 = concatMap varTermPlus es
  xs1 ++ xs2
varTermPlus (_, TermArray dom _) = varTermPlus dom
varTermPlus (_, TermArrayIntro _ es) = do
  concatMap varTermPlus es
varTermPlus (_, TermArrayElim _ xts d e) = varTermPlus d ++ varTermPlus' xts [e]
varTermPlus (_, TermStruct {}) = []
varTermPlus (_, TermStructIntro ets) = concatMap (varTermPlus . fst) ets
varTermPlus (_, TermStructElim xts d e) = do
  let xs = map (\(_, x, _) -> x) xts
  varTermPlus d ++ filter (`notElem` xs) (varTermPlus e)

varTermPlus' :: [IdentifierPlus] -> [TermPlus] -> [Identifier]
varTermPlus' [] es = concatMap varTermPlus es
varTermPlus' ((_, x, t):xts) es = do
  let xs1 = varTermPlus t
  let xs2 = varTermPlus' xts es
  xs1 ++ filter (\y -> y /= x) xs2

substTermPlus :: SubstTerm -> TermPlus -> TermPlus
substTermPlus _ (m, TermTau) = (m, TermTau)
substTermPlus sub (m, TermUpsilon x) =
  fromMaybe (m, TermUpsilon x) (lookup x sub)
substTermPlus sub (m, TermPi xts t) = do
  let (xts', t') = substTermPlusBindingsWithBody sub xts t
  (m, TermPi xts' t')
substTermPlus sub (m, TermPiIntro xts body) = do
  let (xts', body') = substTermPlusBindingsWithBody sub xts body
  (m, TermPiIntro xts' body')
substTermPlus sub (m, TermPiElim e es) = do
  let e' = substTermPlus sub e
  let es' = map (substTermPlus sub) es
  (m, TermPiElim e' es')
substTermPlus sub (m, TermIter (mx, x, t) xts e) = do
  let t' = substTermPlus sub t
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substTermPlusBindingsWithBody sub' xts e
  (m, TermIter (mx, x, t') xts' e')
substTermPlus _ (m, TermConst x) = do
  (m, TermConst x)
substTermPlus sub (m, TermConstDecl (mx, x, t) e) = do
  let t' = substTermPlus sub t
  let e' = substTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m, TermConstDecl (mx, x, t') e')
substTermPlus _ (m, TermFloat16 x) = (m, TermFloat16 x)
substTermPlus _ (m, TermFloat32 x) = (m, TermFloat32 x)
substTermPlus _ (m, TermFloat64 x) = (m, TermFloat64 x)
substTermPlus _ (m, TermEnum x) = (m, TermEnum x)
substTermPlus _ (m, TermEnumIntro l) = (m, TermEnumIntro l)
substTermPlus sub (m, TermEnumElim e branchList) = do
  let e' = substTermPlus sub e
  let (caseList, es) = unzip branchList
  let es' = map (substTermPlus sub) es
  (m, TermEnumElim e' (zip caseList es'))
substTermPlus sub (m, TermArray dom k) = do
  let dom' = substTermPlus sub dom
  (m, TermArray dom' k)
substTermPlus sub (m, TermArrayIntro k es) = do
  let es' = map (substTermPlus sub) es
  (m, TermArrayIntro k es')
substTermPlus sub (m, TermArrayElim mk xts v e) = do
  let v' = substTermPlus sub v
  let (xts', e') = substTermPlusBindingsWithBody sub xts e
  (m, TermArrayElim mk xts' v' e')
substTermPlus _ (m, TermStruct ts) = do
  (m, TermStruct ts)
substTermPlus sub (m, TermStructIntro ets) = do
  let (es, ts) = unzip ets
  let es' = map (substTermPlus sub) es
  (m, TermStructIntro $ zip es' ts)
substTermPlus sub (m, TermStructElim xts v e) = do
  let v' = substTermPlus sub v
  let xs = map (\(_, x, _) -> x) xts
  let sub' = filter (\(k, _) -> k `notElem` xs) sub
  let e' = substTermPlus sub' e
  (m, TermStructElim xts v' e')

substTermPlusBindingsWithBody ::
     SubstTerm -> [IdentifierPlus] -> TermPlus -> ([IdentifierPlus], TermPlus)
substTermPlusBindingsWithBody sub [] e = ([], substTermPlus sub e)
substTermPlusBindingsWithBody sub ((mx, x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substTermPlusBindingsWithBody sub' xts e
  ((mx, x, substTermPlus sub t) : xts', e')

univTerm :: TermPlus
univTerm = (emptyMeta, TermTau)
