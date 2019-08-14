{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Data.WeakTerm where

import           Control.Comonad.Cofree
import           Control.Monad          (forM)
import           Data.IORef
import           Data.Maybe             (fromMaybe)
import           System.IO.Unsafe       (unsafePerformIO)
import           Text.Show.Deriving

import           Data.Basic

data WeakTermF a
  = WeakTermTau
  | WeakTermUpsilon Identifier
  | WeakTermEpsilon Identifier
  | WeakTermEpsilonIntro Literal
  | WeakTermEpsilonElim (Identifier, a)
                        a
                        [(Case, a)]
  | WeakTermPi [(Identifier, a)]
  | WeakTermPiIntro [(Identifier, a)]
                    a
  | WeakTermPiElim a
                   [a]
  | WeakTermSigma [(Identifier, a)]
  | WeakTermSigmaIntro [a]
  | WeakTermSigmaElim [(Identifier, a)]
                      a
                      a
  | WeakTermMu (Identifier, a)
               a
  | WeakTermTheta Identifier
  | WeakTermHole Identifier

type WeakTerm = Cofree WeakTermF WeakMeta

newtype Ref a =
  Ref (IORef a)

data WeakMeta = WeakMeta
  -- The `Ref` here is required to represent "univ : univ".
  { weakMetaType     :: Ref (Maybe WeakTerm)
  -- Location (row, cloumn) of a subterm in a file.
  , weakMetaLocation :: Maybe (Int, Int)
  }

$(deriveShow1 ''WeakTermF)

instance (Show a) => Show (Ref a) where
  show (Ref x) = show $ unsafePerformIO (readIORef x)

deriving instance Show WeakMeta

type SubstWeakTerm = [(Identifier, WeakTerm)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTerm)

varWeakTerm :: WeakTerm -> ([Identifier], [Hole])
varWeakTerm (_ :< WeakTermTau) = ([], [])
varWeakTerm (_ :< WeakTermUpsilon x) = ([x], [])
varWeakTerm (_ :< WeakTermEpsilon _) = ([], [])
varWeakTerm (_ :< WeakTermEpsilonIntro _) = ([], [])
varWeakTerm (_ :< WeakTermEpsilonElim (x, t) e branchList) = do
  let xhs1 = varWeakTerm t
  let xhs2 = varWeakTerm e
  xhss <-
    forM branchList $ \(_, body) -> do
      let (xs, hs) = varWeakTerm body
      return (filter (/= x) xs, hs)
  pairwiseConcat (xhs1 : xhs2 : xhss)
varWeakTerm (_ :< WeakTermPi xts) = varWeakTermBindings xts []
varWeakTerm (_ :< WeakTermPiIntro xts e) = varWeakTermBindings xts [e]
varWeakTerm (_ :< WeakTermPiElim e es) =
  pairwiseConcat $ varWeakTerm e : map varWeakTerm es
varWeakTerm (_ :< WeakTermSigma xts) = varWeakTermBindings xts []
varWeakTerm (_ :< WeakTermSigmaIntro es) = pairwiseConcat $ map varWeakTerm es
varWeakTerm (_ :< WeakTermSigmaElim us e1 e2) =
  pairwiseConcat [varWeakTerm e1, varWeakTermBindings us [e2]]
varWeakTerm (_ :< WeakTermMu ut e) = varWeakTermBindings [ut] [e]
varWeakTerm (_ :< WeakTermTheta _) = ([], [])
varWeakTerm (_ :< WeakTermHole h) = ([], [h])

varWeakTermBindings ::
     [IdentifierPlus] -> [WeakTerm] -> ([Identifier], [Identifier])
varWeakTermBindings [] es = pairwiseConcat $ map varWeakTerm es
varWeakTermBindings ((x, t):xts) es = do
  let (xs1, hs1) = varWeakTerm t
  let (xs2, hs2) = varWeakTermBindings xts es
  (xs1 ++ filter (/= x) xs2, hs1 ++ hs2)

pairwiseConcat :: [([a], [b])] -> ([a], [b])
pairwiseConcat [] = ([], [])
pairwiseConcat ((xs, ys):rest) = do
  let (xs', ys') = pairwiseConcat rest
  (xs ++ xs', ys ++ ys')

substWeakTerm :: SubstWeakTerm -> WeakTerm -> WeakTerm
substWeakTerm _ (m :< WeakTermTau) = m :< WeakTermTau
substWeakTerm sub (m :< WeakTermUpsilon x) =
  fromMaybe (m :< WeakTermUpsilon x) (lookup x sub)
substWeakTerm _ (m :< WeakTermEpsilon x) = m :< WeakTermEpsilon x
substWeakTerm _ (m :< WeakTermEpsilonIntro l) = m :< WeakTermEpsilonIntro l
substWeakTerm sub (m :< WeakTermEpsilonElim (x, t) e branchList) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm sub e
  let (caseList, es) = unzip branchList
  let sub' = filter (\(k, _) -> k /= x) sub
  let es' = map (substWeakTerm sub') es
  m :< WeakTermEpsilonElim (x, t') e' (zip caseList es')
substWeakTerm sub (m :< WeakTermPi xts) = do
  let xts' = substWeakTermBindings sub xts
  m :< WeakTermPi xts'
substWeakTerm sub (m :< WeakTermPiIntro xts body) = do
  let (xts', body') = substWeakTermBindingsWithBody sub xts body
  m :< WeakTermPiIntro xts' body'
substWeakTerm sub (m :< WeakTermPiElim e es) = do
  let e' = substWeakTerm sub e
  let es' = map (substWeakTerm sub) es
  m :< WeakTermPiElim e' es'
substWeakTerm sub (m :< WeakTermSigma xts) = do
  let xts' = substWeakTermBindings sub xts
  m :< WeakTermSigma xts'
substWeakTerm sub (m :< WeakTermSigmaIntro es) = do
  let es' = map (substWeakTerm sub) es
  m :< WeakTermSigmaIntro es'
substWeakTerm sub (m :< WeakTermSigmaElim xts e1 e2) = do
  let e1' = substWeakTerm sub e1
  let (xts', e2') = substWeakTermBindingsWithBody sub xts e2
  m :< WeakTermSigmaElim xts' e1' e2'
substWeakTerm sub (m :< WeakTermMu (x, t) e) = do
  let t' = substWeakTerm sub t
  let e' = substWeakTerm (filter (\(k, _) -> k /= x) sub) e
  m :< WeakTermMu (x, t') e'
substWeakTerm _ (m :< WeakTermTheta t) = m :< WeakTermTheta t
substWeakTerm sub (m :< WeakTermHole s) =
  fromMaybe (m :< WeakTermHole s) (lookup s sub)

substWeakTermBindings :: SubstWeakTerm -> [IdentifierPlus] -> [IdentifierPlus]
substWeakTermBindings _ [] = []
substWeakTermBindings sub ((x, t):xts) = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let xts' = substWeakTermBindings sub' xts
  (x, substWeakTerm sub t) : xts'

substWeakTermBindingsWithBody ::
     SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTerm
  -> ([IdentifierPlus], WeakTerm)
substWeakTermBindingsWithBody sub [] e = ([], substWeakTerm sub e)
substWeakTermBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  let (xts', e') = substWeakTermBindingsWithBody sub' xts e
  ((x, substWeakTerm sub t) : xts', e')

isReducible :: WeakTerm -> Bool
isReducible (_ :< WeakTermTau) = False
isReducible (_ :< WeakTermUpsilon _) = False
isReducible (_ :< WeakTermEpsilon _) = False
isReducible (_ :< WeakTermEpsilonIntro _) = False
isReducible (_ :< WeakTermEpsilonElim _ (_ :< WeakTermEpsilonIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseLiteral l `elem` caseList || CaseDefault `elem` caseList
isReducible (_ :< WeakTermEpsilonElim (_, _) e _) = isReducible e
isReducible (_ :< WeakTermPi _) = False
isReducible (_ :< WeakTermPiIntro {}) = False
isReducible (_ :< WeakTermPiElim (_ :< WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_ :< WeakTermPiElim (_ :< WeakTermMu _ _) _) = True -- CBV recursion
isReducible (_ :< WeakTermPiElim (_ :< WeakTermTheta c) [_ :< WeakTermEpsilonIntro (LiteralInteger _), _ :< WeakTermEpsilonIntro (LiteralInteger _)]) -- constant application
  | c `elem` intArithConstantList = True
isReducible (_ :< WeakTermPiElim e es) = isReducible e || any isReducible es
isReducible (_ :< WeakTermSigma _) = False
isReducible (_ :< WeakTermSigmaIntro es) = any isReducible es
isReducible (_ :< WeakTermSigmaElim xts (_ :< WeakTermSigmaIntro es) _)
  | length xts == length es = True
isReducible (_ :< WeakTermSigmaElim _ e1 _) = isReducible e1
isReducible (_ :< WeakTermMu _ _) = False
isReducible (_ :< WeakTermTheta _) = False
isReducible (_ :< WeakTermHole _) = False

isValue :: WeakTerm -> Bool
isValue (_ :< WeakTermTau)            = True
isValue (_ :< WeakTermUpsilon _)      = True
isValue (_ :< WeakTermEpsilon _)      = True
isValue (_ :< WeakTermEpsilonIntro _) = True
isValue (_ :< WeakTermPi {})          = True
isValue (_ :< WeakTermPiIntro {})     = True
isValue (_ :< WeakTermSigma {})       = True
isValue (_ :< WeakTermSigmaIntro es)  = all isValue es
isValue _                             = False
