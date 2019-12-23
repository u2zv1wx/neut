{-# LANGUAGE FlexibleContexts #-}

module Data.WeakTerm where

import Control.Monad.Except
import Data.IORef
import Data.Maybe (fromMaybe)
import Numeric.Half
import System.IO.Unsafe (unsafePerformIO)

import Data.Basic

data WeakTerm
  = WeakTermTau
  | WeakTermTheta Identifier
  | WeakTermUpsilon Identifier
  | WeakTermPi [IdentifierPlus] WeakTermPlus
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
  | WeakTermEnum EnumType
  | WeakTermEnumIntro EnumValue
  | WeakTermEnumElim WeakTermPlus [(Case, WeakTermPlus)]
  | WeakTermArray ArrayKind WeakTermPlus WeakTermPlus
  | WeakTermArrayIntro ArrayKind [(EnumValue, WeakTermPlus)]
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
varWeakTermPlus (_, WeakTermPi xts t) = varWeakTermPlusBindings xts [t]
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
varWeakTermPlus (_, WeakTermEnum _) = ([], [])
varWeakTermPlus (_, WeakTermEnumIntro _) = ([], [])
varWeakTermPlus (_, WeakTermEnumElim e branchList) = do
  let xhs = varWeakTermPlus e
  let xhss = map (\(_, body) -> varWeakTermPlus body) branchList
  pairwiseConcat (xhs : xhss)
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

substWeakTermPlus ::
     (MonadIO m, MonadError String m)
  => SubstWeakTerm
  -> WeakTermPlus
  -> m WeakTermPlus
substWeakTermPlus sub (m, WeakTermTau) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermTau)
substWeakTermPlus sub (m, WeakTermTheta t) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermTheta t)
substWeakTermPlus sub (m, WeakTermUpsilon x) = do
  m' <- substWeakMeta sub m
  return $ fromMaybe (m', WeakTermUpsilon x) (lookup x sub)
substWeakTermPlus sub (m, WeakTermPi xts t) = do
  m' <- substWeakMeta sub m
  (xts', t') <- substWeakTermPlusBindingsWithBody sub xts t
  return (m', WeakTermPi xts' t')
substWeakTermPlus sub (m, WeakTermPiIntro xts body) = do
  m' <- substWeakMeta sub m
  (xts', body') <- substWeakTermPlusBindingsWithBody sub xts body
  return (m', WeakTermPiIntro xts' body')
substWeakTermPlus sub (m, WeakTermPiElim e es) = do
  m' <- substWeakMeta sub m
  e' <- substWeakTermPlus sub e
  es' <- mapM (substWeakTermPlus sub) es
  return (m', WeakTermPiElim e' es')
substWeakTermPlus sub (m, WeakTermMu (x, t) e) = do
  m' <- substWeakMeta sub m
  t' <- substWeakTermPlus sub t
  e' <- substWeakTermPlus (filter (\(k, _) -> k /= x) sub) e
  return (m', WeakTermMu (x, t') e')
substWeakTermPlus sub (m, WeakTermZeta s) = do
  m' <- substWeakMeta sub m
  return $ fromMaybe (m', WeakTermZeta s) (lookup s sub)
substWeakTermPlus sub (m, WeakTermIntS size x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermIntS size x)
substWeakTermPlus sub (m, WeakTermIntU size x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermIntU size x)
substWeakTermPlus sub (m, WeakTermInt x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermInt x)
substWeakTermPlus sub (m, WeakTermFloat16 x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat16 x)
substWeakTermPlus sub (m, WeakTermFloat32 x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat32 x)
substWeakTermPlus sub (m, WeakTermFloat64 x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat64 x)
substWeakTermPlus sub (m, WeakTermFloat x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermFloat x)
substWeakTermPlus sub (m, WeakTermEnum x) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermEnum x)
substWeakTermPlus sub (m, WeakTermEnumIntro l) = do
  m' <- substWeakMeta sub m
  return (m', WeakTermEnumIntro l)
substWeakTermPlus sub (m, WeakTermEnumElim e branchList) = do
  m' <- substWeakMeta sub m
  e' <- substWeakTermPlus sub e
  let (caseList, es) = unzip branchList
  es' <- mapM (substWeakTermPlus sub) es
  return (m', WeakTermEnumElim e' (zip caseList es'))
substWeakTermPlus sub (m, WeakTermArray kind from to) = do
  m' <- substWeakMeta sub m
  from' <- substWeakTermPlus sub from
  to' <- substWeakTermPlus sub to
  return (m', WeakTermArray kind from' to')
substWeakTermPlus sub (m, WeakTermArrayIntro kind les) = do
  m' <- substWeakMeta sub m
  let (ls, es) = unzip les
  es' <- mapM (substWeakTermPlus sub) es
  return (m', WeakTermArrayIntro kind (zip ls es'))
substWeakTermPlus sub (m, WeakTermArrayElim kind e1 e2) = do
  m' <- substWeakMeta sub m
  e1' <- substWeakTermPlus sub e1
  e2' <- substWeakTermPlus sub e2
  return (m', WeakTermArrayElim kind e1' e2')

substWeakTermPlusBindingsWithBody ::
     (MonadIO m, MonadError String m)
  => SubstWeakTerm
  -> [IdentifierPlus]
  -> WeakTermPlus
  -> m ([IdentifierPlus], WeakTermPlus)
substWeakTermPlusBindingsWithBody sub [] e = do
  e' <- substWeakTermPlus sub e
  return ([], e')
substWeakTermPlusBindingsWithBody sub ((x, t):xts) e = do
  let sub' = filter (\(k, _) -> k /= x) sub
  (xts', e') <- substWeakTermPlusBindingsWithBody sub' xts e
  t' <- substWeakTermPlus sub t
  return ((x, t') : xts', e')

substWeakMeta ::
     (MonadIO m, MonadError String m) => SubstWeakTerm -> WeakMeta -> m WeakMeta
substWeakMeta _ m@(WeakMetaTerminal _) = return m
substWeakMeta sub (WeakMetaNonTerminal (Ref ref) ml) = do
  mt <- liftIO $ readIORef ref
  case mt of
    Nothing -> throwError "substWeakMeta for Nothing"
    Just t -> do
      t' <- substWeakTermPlus sub t
      liftIO $ writeIORef ref (Just t')
      return $ WeakMetaNonTerminal (Ref ref) ml

isReducible :: WeakTermPlus -> Bool
isReducible (_, WeakTermTau) = False
isReducible (_, WeakTermTheta _) = False
isReducible (_, WeakTermUpsilon _) = False
isReducible (_, WeakTermPi _ _) = False
isReducible (_, WeakTermPiIntro {}) = False
isReducible (_, WeakTermPiElim (_, WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_, WeakTermPiElim (_, WeakTermMu _ _) _) = True -- CBV recursion
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntS _ _), (_, WeakTermIntS _ _)])
  | [typeStr, opStr] <- wordsBy '.' c
  , Just (LowTypeIntS _) <- asLowTypeMaybe typeStr
  , Just arith <- asBinaryOpMaybe' opStr
  , isArithOp arith = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntU _ _), (_, WeakTermIntU _ _)])
  | [typeStr, opStr] <- wordsBy '.' c
  , Just (LowTypeIntU _) <- asLowTypeMaybe typeStr
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
isReducible (_, WeakTermEnum _) = False
isReducible (_, WeakTermEnumIntro _) = False
isReducible (_, WeakTermEnumElim (_, WeakTermEnumIntro l) branchList) = do
  let (caseList, _) = unzip branchList
  CaseValue l `elem` caseList || CaseDefault `elem` caseList
isReducible (_, WeakTermEnumElim e _) = isReducible e
isReducible (_, WeakTermArray {}) = False
isReducible (_, WeakTermArrayIntro _ les) = any isReducible $ map snd les
isReducible (_, WeakTermArrayElim _ (_, WeakTermArrayIntro _ les) (_, WeakTermEnumIntro l))
  | l `elem` map fst les = True
isReducible (_, WeakTermArrayElim _ e1 e2) = isReducible e1 || isReducible e2

isValue :: WeakTermPlus -> Bool
isValue (_, WeakTermTau) = True
isValue (_, WeakTermUpsilon _) = True
isValue (_, WeakTermPi {}) = True
isValue (_, WeakTermPiIntro {}) = True
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
