module Data.WeakTerm where

import Data.IORef
import Data.Maybe (fromMaybe)
import Numeric.Half
import System.IO.Unsafe (unsafePerformIO)

import Data.Basic

data WeakTerm
  = WeakTermTau
  | WeakTermTheta Identifier
  | WeakTermUpsilon Identifier
  | WeakTermEpsilon Identifier
  | WeakTermEpsilonIntro Identifier
  | WeakTermEpsilonElim WeakTermPlus [(Case, WeakTermPlus)]
  | WeakTermPi [IdentifierPlus]
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
  | WeakTermArray ArrayKind WeakTermPlus WeakTermPlus
  | WeakTermArrayIntro ArrayKind [(EpsilonLabel, WeakTermPlus)]
  | WeakTermArrayElim ArrayKind WeakTermPlus WeakTermPlus
  deriving (Show)

newtype Ref a =
  Ref (IORef a)

data WeakMeta
  = WeakMetaTerminal (Maybe Loc)
  | WeakMetaNonTerminal (Ref (Maybe WeakTermPlus)) (Maybe Loc)
  deriving (Show)

type WeakTermPlus = (WeakMeta, WeakTerm)

instance (Show a) => Show (Ref a) where
  show (Ref x) = show $ unsafePerformIO $ readIORef x

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTermPlus)

varWeakTermPlus :: WeakTermPlus -> ([Identifier], [Hole])
varWeakTermPlus (_, WeakTermTau) = ([], [])
varWeakTermPlus (_, WeakTermTheta _) = ([], [])
varWeakTermPlus (_, WeakTermUpsilon x) = ([x], [])
varWeakTermPlus (_, WeakTermEpsilon _) = ([], [])
varWeakTermPlus (_, WeakTermEpsilonIntro _) = ([], [])
varWeakTermPlus (_, WeakTermEpsilonElim e branchList) = do
  let xhs = varWeakTermPlus e
  let xhss = map (\(_, body) -> varWeakTermPlus body) branchList
  pairwiseConcat (xhs : xhss)
varWeakTermPlus (_, WeakTermPi xts) = varWeakTermPlusBindings xts []
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

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substWeakTermPlus :: SubstWeakTerm -> WeakTermPlus -> WeakTermPlus
substWeakTermPlus _ (m, WeakTermTau) = (m, WeakTermTau)
substWeakTermPlus _ (m, WeakTermTheta t) = (m, WeakTermTheta t)
substWeakTermPlus sub (m, WeakTermUpsilon x) =
  fromMaybe (m, WeakTermUpsilon x) (lookup x sub)
substWeakTermPlus _ (m, WeakTermEpsilon x) = (m, WeakTermEpsilon x)
substWeakTermPlus _ (m, WeakTermEpsilonIntro l) = (m, WeakTermEpsilonIntro l)
substWeakTermPlus sub (m, WeakTermEpsilonElim e branchList) = do
  let e' = substWeakTermPlus sub e
  let (caseList, es) = unzip branchList
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermEpsilonElim e' (zip caseList es'))
substWeakTermPlus sub (m, WeakTermPi xts) = do
  let xts' = substWeakTermPlusBindings sub xts
  (m, WeakTermPi xts')
substWeakTermPlus sub (m, WeakTermPiIntro xts body) = do
  let (xts', body') = substWeakTermPlusBindingsWithBody sub xts body
  (m, WeakTermPiIntro xts' body')
substWeakTermPlus sub (m, WeakTermPiElim e es) = do
  let e' = substWeakTermPlus sub e
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermPiElim e' es')
substWeakTermPlus sub (m, WeakTermMu (x, t) e) = do
  let t' = substWeakTermPlus sub t
  let e' = substWeakTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m, WeakTermMu (x, t') e')
substWeakTermPlus sub (m, WeakTermZeta s) =
  fromMaybe (m, WeakTermZeta s) (lookup s sub)
substWeakTermPlus _ (m, WeakTermIntS size x) = (m, WeakTermIntS size x)
substWeakTermPlus _ (m, WeakTermIntU size x) = (m, WeakTermIntU size x)
substWeakTermPlus _ (m, WeakTermInt x) = (m, WeakTermInt x)
substWeakTermPlus _ (m, WeakTermFloat16 x) = (m, WeakTermFloat16 x)
substWeakTermPlus _ (m, WeakTermFloat32 x) = (m, WeakTermFloat32 x)
substWeakTermPlus _ (m, WeakTermFloat64 x) = (m, WeakTermFloat64 x)
substWeakTermPlus _ (m, WeakTermFloat x) = (m, WeakTermFloat x)
substWeakTermPlus sub (m, WeakTermArray kind from to) = do
  let from' = substWeakTermPlus sub from
  let to' = substWeakTermPlus sub to
  (m, WeakTermArray kind from' to')
substWeakTermPlus sub (m, WeakTermArrayIntro kind les) = do
  let (ls, es) = unzip les
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermArrayIntro kind (zip ls es'))
substWeakTermPlus sub (m, WeakTermArrayElim kind e1 e2) = do
  let e1' = substWeakTermPlus sub e1
  let e2' = substWeakTermPlus sub e2
  (m, WeakTermArrayElim kind e1' e2')

substWeakTermPlusBindings ::
     SubstWeakTerm -> [IdentifierPlus] -> [IdentifierPlus]
substWeakTermPlusBindings _ [] = []
substWeakTermPlusBindings sub ((x, t):xts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let xts' = substWeakTermPlusBindings sub' xts
  (x, substWeakTermPlus sub t) : xts'

substWeakTermPlusBindingsWithBody ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> ([IdentifierPlus], WeakTermPlus)
substWeakTermPlusBindingsWithBody sub [] e = ([], substWeakTermPlus sub e)
substWeakTermPlusBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermPlusBindingsWithBody sub' xts e
  ((x, substWeakTermPlus sub t) : xts', e')

isReducible :: WeakTermPlus -> Bool
isReducible (_, WeakTermTau) = False
isReducible (_, WeakTermTheta _) = False
isReducible (_, WeakTermUpsilon _) = False
isReducible (_, WeakTermEpsilon _) = False
isReducible (_, WeakTermEpsilonIntro _) = False
isReducible (_, WeakTermEpsilonElim (_, WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLabel l `elem` caseList || CaseDefault `elem` caseList
isReducible (_, WeakTermEpsilonElim e _) = isReducible e
isReducible (_, WeakTermPi _) = False
isReducible (_, WeakTermPiIntro {}) = False
isReducible (_, WeakTermPiElim (_, WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_, WeakTermPiElim (_, WeakTermMu _ _) _) = True -- CBV recursion
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntS _ _), (_, WeakTermIntS _ _)])
  | [typeStr, opStr] <- wordsBy '.' c
  , Just (LowTypeSignedInt _) <- asLowTypeMaybe typeStr
  , Just arith <- asBinaryOpMaybe' opStr
  , isArithOp arith = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntU _ _), (_, WeakTermIntU _ _)])
  | [typeStr, opStr] <- wordsBy '.' c
  , Just (LowTypeUnsignedInt _) <- asLowTypeMaybe typeStr
  , Just arith <- asBinaryOpMaybe' opStr
  , isArithOp arith = True
-- FIXME: isReducible for Float
-- FIXME: rewrite here using asBinaryOpMaybe
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat16 _), (_, WeakTermFloat16 _)])
  | [typeStr, opStr] <- wordsBy '.' c
  , Just (LowTypeFloat FloatSize16) <- asLowTypeMaybe typeStr
  , Just arith <- asBinaryOpMaybe' opStr
  , isArithOp arith = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat32 _), (_, WeakTermFloat32 _)])
  | [typeStr, opStr] <- wordsBy '.' c
  , Just (LowTypeFloat FloatSize32) <- asLowTypeMaybe typeStr
  , Just arith <- asBinaryOpMaybe' opStr
  , isArithOp arith = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat64 _), (_, WeakTermFloat64 _)])
  | [typeStr, opStr] <- wordsBy '.' c
  , Just (LowTypeFloat FloatSize64) <- asLowTypeMaybe typeStr
  , Just arith <- asBinaryOpMaybe' opStr
  , isArithOp arith = True
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
isReducible (_, WeakTermArray {}) = False
isReducible (_, WeakTermArrayIntro _ les) = any isReducible $ map snd les
isReducible (_, WeakTermArrayElim _ (_, WeakTermArrayIntro _ les) (_, WeakTermEpsilonIntro l))
  | l `elem` map fst les = True
isReducible (_, WeakTermArrayElim _ e1 e2) = isReducible e1 || isReducible e2

isValue :: WeakTermPlus -> Bool
isValue (_, WeakTermTau) = True
isValue (_, WeakTermUpsilon _) = True
isValue (_, WeakTermEpsilon _) = True
isValue (_, WeakTermEpsilonIntro _) = True
isValue (_, WeakTermPi {}) = True
isValue (_, WeakTermPiIntro {}) = True
isValue (_, WeakTermIntS _ _) = True
isValue (_, WeakTermIntU _ _) = True
isValue (_, WeakTermInt _) = True
isValue (_, WeakTermFloat16 _) = True
isValue (_, WeakTermFloat32 _) = True
isValue (_, WeakTermFloat64 _) = True
isValue (_, WeakTermFloat _) = True
isValue (_, WeakTermArray {}) = True
isValue (_, WeakTermArrayIntro _ les) = all isValue $ map snd les
isValue _ = False
