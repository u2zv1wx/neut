module Data.Term where

import Control.Monad (forM)
import Data.List (nubBy)
import Data.Maybe (fromMaybe)
import Numeric.Half

import Data.Basic

data Term
  = TermTau
  | TermTheta Identifier
  | TermUpsilon Identifier
  | TermPi [IdentifierPlus] TermPlus
  | TermPiIntro [IdentifierPlus] TermPlus
  | TermPiElim TermPlus [TermPlus]
  | TermMu (Identifier, TermPlus) TermPlus
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

-- data Meta
--   = MetaTerminal (Meta)
--   | MetaNonTerminal TermPlus (Meta)
--   -- deriving (Show)
-- instance Show Meta where
--   show _ = "_"
type TermPlus = (Meta, Term)

type SubstTerm = [(Identifier, TermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, TermPlus)

-- obtainInfoMeta :: Meta -> (TermPlus, Meta)
-- obtainInfoMeta (MetaTerminal ml) = ((MetaTerminal ml, TermTau), ml)
-- obtainInfoMeta (MetaNonTerminal t ml) = (t, ml)
toTermUpsilon :: Identifier -> TermPlus
toTermUpsilon x = do
  (emptyMeta, TermUpsilon x)

toTermInt64 :: Integer -> TermPlus
toTermInt64 i = (emptyMeta, TermIntS 64 i)

varTermPlus :: TermPlus -> [(Identifier, Meta, TermPlus)]
varTermPlus e = nubBy (\(x, _, _) (y, _, _) -> x == y) $ getClosedVarChain e

getClosedVarChain :: TermPlus -> [(Identifier, Meta, TermPlus)]
getClosedVarChain (_, TermTau) = []
getClosedVarChain (_, TermTheta _) = []
getClosedVarChain (_, TermUpsilon _) = undefined
  -- case m of
  --   MetaTerminal ml -> [(x, ml, (m, TermTau))]
  --   MetaNonTerminal t ml -> getClosedVarChain t ++ [(x, ml, t)]
getClosedVarChain (_, TermPi xts t) = getClosedVarChainBindings xts [t]
getClosedVarChain (_, TermPiIntro xts e) = getClosedVarChainBindings xts [e]
getClosedVarChain (_, TermPiElim e es) =
  getClosedVarChain e ++ concatMap getClosedVarChain es
getClosedVarChain (_, TermMu ut e) = getClosedVarChainBindings [ut] [e]
getClosedVarChain (_, TermIntS _ _) = []
getClosedVarChain (_, TermIntU _ _) = []
getClosedVarChain (_, TermFloat16 _) = []
getClosedVarChain (_, TermFloat32 _) = []
getClosedVarChain (_, TermFloat64 _) = []
getClosedVarChain (_, TermEnum _) = []
getClosedVarChain (_, TermEnumIntro _) = []
getClosedVarChain (_, TermEnumElim e branchList) = do
  let xhs = getClosedVarChain e
  xhss <- forM branchList $ \(_, body) -> do return $ getClosedVarChain body
  concat (xhs : xhss)
getClosedVarChain (_, TermArray _ indexType) = getClosedVarChain indexType
getClosedVarChain (_, TermArrayIntro _ les) = do
  let (_, es) = unzip les
  concat $ map getClosedVarChain es
getClosedVarChain (_, TermArrayElim _ e1 e2) = do
  getClosedVarChain e1 ++ getClosedVarChain e2

getClosedVarChainBindings ::
     [(Identifier, TermPlus)] -> [TermPlus] -> [(Identifier, Meta, TermPlus)]
getClosedVarChainBindings [] es = concatMap getClosedVarChain es
getClosedVarChainBindings ((x, t):xts) es = do
  let xs1 = getClosedVarChain t
  let xs2 = getClosedVarChainBindings xts es
  xs1 ++ filter (\(y, _, _) -> y /= x) xs2

substTermPlus :: SubstTerm -> TermPlus -> TermPlus
substTermPlus _ (m, TermTau) = (m, TermTau)
substTermPlus _ (m, TermTheta t) = (m, TermTheta t)
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
substTermPlus sub (m, TermMu (x, t) e) = do
  let t' = substTermPlus sub t
  let e' = substTermPlus (filter (\(k, _) -> k /= x) sub) e
  (m, TermMu (x, t') e')
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

-- substMeta :: SubstTerm -> Meta -> Meta
-- substMeta _ (MetaTerminal ml) = MetaTerminal ml
-- substMeta sub (MetaNonTerminal t ml) = MetaNonTerminal (substTermPlus sub t) ml
isValue :: TermPlus -> Bool
isValue (_, TermTau) = True
isValue (_, TermUpsilon _) = True
isValue (_, TermPi {}) = True
isValue (_, TermPiIntro {}) = True
isValue (_, TermEnum _) = True
isValue (_, TermEnumIntro _) = True
isValue _ = False
