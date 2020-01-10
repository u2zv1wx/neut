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
  | TermIntS IntSize Integer
  | TermIntU IntSize Integer
  | TermFloat16 Half
  | TermFloat32 Float
  | TermFloat64 Double
  | TermEnum EnumType
  | TermEnumIntro EnumValue
  | TermEnumElim TermPlus [(Case, TermPlus)]
  | TermArray ArrayKind TermPlus
  | TermArrayIntro ArrayKind [(EnumValue, TermPlus)]
  | TermArrayElim ArrayKind TermPlus TermPlus
  deriving (Show)

type TermPlus = (Meta, Term)

type SubstTerm = [(Identifier, TermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, TermPlus)

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
varTermPlus (_, TermIter (x, t) xts e) =
  varTermPlus t ++ filter (/= x) (varTermPlus' xts [e])
varTermPlus (_, TermConst _) = []
varTermPlus (_, TermConstDecl xt e) = varTermPlus' [xt] [e]
varTermPlus (_, TermIntS _ _) = []
varTermPlus (_, TermIntU _ _) = []
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
varTermPlus (_, TermArray _ indexType) = varTermPlus indexType
varTermPlus (_, TermArrayIntro _ les) = do
  let es = map snd les
  concatMap varTermPlus es
varTermPlus (_, TermArrayElim _ e1 e2) = do
  let xs1 = varTermPlus e1
  let xs2 = varTermPlus e2
  xs1 ++ xs2

varTermPlus' :: [(Identifier, TermPlus)] -> [TermPlus] -> [Identifier]
varTermPlus' [] es = concatMap varTermPlus es
varTermPlus' ((x, t):xts) es = do
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
substTermPlus sub (m, TermIter (x, t) xts e) = do
  let t' = substTermPlus sub t
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substTermPlusBindingsWithBody sub' xts e
  (m, TermIter (x, t') xts' e')
substTermPlus _ (m, TermConst x) = do
  (m, TermConst x)
substTermPlus sub (m, TermConstDecl (x, t) e) = do
  let t' = substTermPlus sub t
  let e' = substTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m, TermConstDecl (x, t') e')
substTermPlus _ (m, TermIntS size x) = (m, TermIntS size x)
substTermPlus _ (m, TermIntU size x) = (m, TermIntU size x)
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
substTermPlus sub (m, TermArray k indexType) = do
  let indexType' = substTermPlus sub indexType
  (m, TermArray k indexType')
substTermPlus sub (m, TermArrayIntro k les) = do
  let (ls, es) = unzip les
  let es' = map (substTermPlus sub) es
  (m, TermArrayIntro k (zip ls es'))
substTermPlus sub (m, TermArrayElim k e1 e2) = do
  let e1' = substTermPlus sub e1
  let e2' = substTermPlus sub e2
  (m, TermArrayElim k e1' e2')

substTermPlusBindingsWithBody ::
     SubstTerm -> [IdentifierPlus] -> TermPlus -> ([IdentifierPlus], TermPlus)
substTermPlusBindingsWithBody sub [] e = ([], substTermPlus sub e)
substTermPlusBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substTermPlusBindingsWithBody sub' xts e
  ((x, substTermPlus sub t) : xts', e')

isValue :: TermPlus -> Bool
isValue (_, TermTau) = True
isValue (_, TermUpsilon _) = True
isValue (_, TermPi {}) = True
isValue (_, TermPiIntro {}) = True
isValue (_, TermIter {}) = True
isValue (_, TermIntS _ _) = True
isValue (_, TermIntU _ _) = True
isValue (_, TermFloat16 _) = True
isValue (_, TermFloat32 _) = True
isValue (_, TermFloat64 _) = True
isValue (_, TermEnum _) = True
isValue (_, TermEnumIntro _) = True
isValue (_, TermArray {}) = True
isValue (_, TermArrayIntro _ les) = all isValue $ map snd les
isValue _ = False

univTerm :: TermPlus
univTerm = (emptyMeta, TermTau)
