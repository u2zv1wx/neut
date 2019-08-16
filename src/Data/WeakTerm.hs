module Data.WeakTerm where

import           Control.Monad    (forM)
import           Data.IORef
import           Data.Maybe       (fromMaybe)
import           System.IO.Unsafe (unsafePerformIO)

import           Data.Basic

data WeakTerm
  = WeakTermTau
  | WeakTermTheta Identifier
  | WeakTermUpsilon Identifier
  | WeakTermEpsilon Identifier
  | WeakTermEpsilonIntro Literal
  | WeakTermEpsilonElim (Identifier, WeakTermPlus)
                        WeakTermPlus
                        [(Case, WeakTermPlus)]
  | WeakTermPi [(Identifier, WeakTermPlus)]
  | WeakTermPiIntro [(Identifier, WeakTermPlus)]
                    WeakTermPlus
  | WeakTermPiElim WeakTermPlus
                   [WeakTermPlus]
  | WeakTermSigma [(Identifier, WeakTermPlus)]
  | WeakTermSigmaIntro [WeakTermPlus]
  | WeakTermSigmaElim [(Identifier, WeakTermPlus)]
                      WeakTermPlus
                      WeakTermPlus
  | WeakTermMu (Identifier, WeakTermPlus)
               WeakTermPlus
  | WeakTermZeta Identifier
  deriving (Show)

newtype Ref a =
  Ref (IORef a)

data WeakMeta
  = WeakMetaTerminal (Maybe (Int, Int))
  | WeakMetaNonTerminal (Ref (Maybe WeakTermPlus))
                        (Maybe (Int, Int))
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
varWeakTermPlus (_, WeakTermEpsilonElim (x, t) e branchList) = do
  let xhs1 = varWeakTermPlus t
  let xhs2 = varWeakTermPlus e
  xhss <-
    forM branchList $ \(_, body) -> do
      let (xs, hs) = varWeakTermPlus body
      return (filter (/= x) xs, hs)
  pairwiseConcat (xhs1 : xhs2 : xhss)
varWeakTermPlus (_, WeakTermPi xts) = varWeakTermPlusBindings xts []
varWeakTermPlus (_, WeakTermPiIntro xts e) = varWeakTermPlusBindings xts [e]
varWeakTermPlus (_, WeakTermPiElim e es) =
  pairwiseConcat $ varWeakTermPlus e : map varWeakTermPlus es
varWeakTermPlus (_, WeakTermSigma xts) = varWeakTermPlusBindings xts []
varWeakTermPlus (_, WeakTermSigmaIntro es) =
  pairwiseConcat $ map varWeakTermPlus es
varWeakTermPlus (_, WeakTermSigmaElim us e1 e2) =
  pairwiseConcat [varWeakTermPlus e1, varWeakTermPlusBindings us [e2]]
varWeakTermPlus (_, WeakTermMu ut e) = varWeakTermPlusBindings [ut] [e]
varWeakTermPlus (_, WeakTermZeta h) = ([], [h])

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
substWeakTermPlus sub (m, WeakTermEpsilonElim (x, t) e branchList) = do
  let t' = substWeakTermPlus sub t
  let e' = substWeakTermPlus sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakTermPlus sub') es
  (m, WeakTermEpsilonElim (x, t') e' (zip caseList es'))
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
substWeakTermPlus sub (m, WeakTermSigma xts) = do
  let xts' = substWeakTermPlusBindings sub xts
  (m, WeakTermSigma xts')
substWeakTermPlus sub (m, WeakTermSigmaIntro es) = do
  let es' = map (substWeakTermPlus sub) es
  (m, WeakTermSigmaIntro es')
substWeakTermPlus sub (m, WeakTermSigmaElim xts e1 e2) = do
  let e1' = substWeakTermPlus sub e1
  let (xts', e2') = substWeakTermPlusBindingsWithBody sub xts e2
  (m, WeakTermSigmaElim xts' e1' e2')
substWeakTermPlus sub (m, WeakTermMu (x, t) e) = do
  let t' = substWeakTermPlus sub t
  let e' = substWeakTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m, WeakTermMu (x, t') e')
substWeakTermPlus sub (m, WeakTermZeta s) =
  fromMaybe (m, WeakTermZeta s) (lookup s sub)

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
isReducible (_, WeakTermEpsilonElim _ (_, WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_, WeakTermEpsilonElim (_, _) e _) = isReducible e
isReducible (_, WeakTermPi _) = False
isReducible (_, WeakTermPiIntro {}) = False
isReducible (_, WeakTermPiElim (_, WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_, WeakTermPiElim (_, WeakTermMu _ _) _) = True -- CBV recursion
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermEpsilonIntro (LiteralInteger _)), (_, WeakTermEpsilonIntro (LiteralInteger _))]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_, WeakTermPiElim e es) = isReducible e || any isReducible es
isReducible (_, WeakTermSigma _) = False
isReducible (_, WeakTermSigmaIntro es) = any isReducible es
isReducible (_, WeakTermSigmaElim xts (_, WeakTermSigmaIntro es) _)
  | length xts == length es = True
isReducible (_, WeakTermSigmaElim _ e1 _) = isReducible e1
isReducible (_, WeakTermMu _ _) = False
isReducible (_, WeakTermZeta _) = False

isValue :: WeakTermPlus -> Bool
isValue (_, WeakTermTau)            = True
isValue (_, WeakTermUpsilon _)      = True
isValue (_, WeakTermEpsilon _)      = True
isValue (_, WeakTermEpsilonIntro _) = True
isValue (_, WeakTermPi {})          = True
isValue (_, WeakTermPiIntro {})     = True
isValue (_, WeakTermSigma {})       = True
isValue (_, WeakTermSigmaIntro es)  = all isValue es
isValue _                           = False
