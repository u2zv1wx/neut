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

instance Show WeakMeta where
  show _ = "_"

type WeakTermPlus = (WeakMeta, WeakTerm)

type SubstWeakTerm = [(Identifier, WeakTermPlus)]

type Hole = Identifier

type IdentifierPlus = (Identifier, WeakTermPlus)

newtype WeakTermRef =
  WeakTermRef (IORef (Maybe WeakTermPlus))

data WeakMeta
  = WeakMetaTerminal (Maybe Loc)
  | WeakMetaNonTerminal WeakTermRef (Maybe Loc)
  -- deriving (Show)

instance Show WeakTermRef where
  show (WeakTermRef x) = show $ unsafePerformIO $ readIORef x

varWeakTermPlus ::
     (MonadIO m, MonadError String m)
  => WeakTermPlus
  -> m ([Identifier], [Hole])
varWeakTermPlus (m, WeakTermTau) = varWeakMeta m
varWeakTermPlus (m, WeakTermTheta _) = varWeakMeta m
varWeakTermPlus (m, WeakTermUpsilon x) = do
  xhs <- varWeakMeta m
  return $ pairwiseConcat [([x], []), xhs]
varWeakTermPlus (m, WeakTermPi xts t) = do
  xhs <- varWeakTermPlusBindings xts [t]
  yhs <- varWeakMeta m
  return $ pairwiseConcat [xhs, yhs]
varWeakTermPlus (m, WeakTermPiIntro xts e) = do
  xhs <- varWeakTermPlusBindings xts [e]
  yhs <- varWeakMeta m
  return $ pairwiseConcat [xhs, yhs]
varWeakTermPlus (m, WeakTermPiElim e es) = do
  xhs <- varWeakTermPlus e
  yhss <- mapM varWeakTermPlus es
  zhs <- varWeakMeta m
  return $ pairwiseConcat $ xhs : zhs : yhss
varWeakTermPlus (m, WeakTermMu ut e) = do
  xhs <- varWeakTermPlusBindings [ut] [e]
  yhs <- varWeakMeta m
  return $ pairwiseConcat [xhs, yhs]
varWeakTermPlus (m, WeakTermZeta h) = do
  xhs <- varWeakMeta m
  return $ pairwiseConcat [([], [h]), xhs]
varWeakTermPlus (m, WeakTermIntS _ _) = varWeakMeta m
varWeakTermPlus (m, WeakTermIntU _ _) = varWeakMeta m
varWeakTermPlus (m, WeakTermInt _) = varWeakMeta m
varWeakTermPlus (m, WeakTermFloat16 _) = varWeakMeta m
varWeakTermPlus (m, WeakTermFloat32 _) = varWeakMeta m
varWeakTermPlus (m, WeakTermFloat64 _) = varWeakMeta m
varWeakTermPlus (m, WeakTermFloat _) = varWeakMeta m
varWeakTermPlus (m, WeakTermEnum _) = varWeakMeta m
varWeakTermPlus (m, WeakTermEnumIntro _) = varWeakMeta m
varWeakTermPlus (m, WeakTermEnumElim e les) = do
  xhs <- varWeakTermPlus e
  xhss <- mapM (\(_, body) -> varWeakTermPlus body) les
  yhs <- varWeakMeta m
  return $ pairwiseConcat $ xhs : yhs : xhss
varWeakTermPlus (m, WeakTermArray _ e1 e2) = do
  xhs1 <- varWeakTermPlus e1
  xhs2 <- varWeakTermPlus e2
  xhs3 <- varWeakMeta m
  return $ pairwiseConcat [xhs1, xhs2, xhs3]
varWeakTermPlus (m, WeakTermArrayIntro _ les) = do
  xhs <- varWeakMeta m
  xhss <- mapM (\(_, body) -> varWeakTermPlus body) les
  return $ pairwiseConcat $ xhs : xhss
varWeakTermPlus (m, WeakTermArrayElim _ e1 e2) = do
  xhs1 <- varWeakTermPlus e1
  xhs2 <- varWeakTermPlus e2
  xhs3 <- varWeakMeta m
  return $ pairwiseConcat [xhs1, xhs2, xhs3]

varWeakTermPlusBindings ::
     (MonadIO m, MonadError String m)
  => [IdentifierPlus]
  -> [WeakTermPlus]
  -> m ([Identifier], [Hole])
varWeakTermPlusBindings [] es = do
  xhss <- mapM varWeakTermPlus es
  return $ pairwiseConcat xhss
varWeakTermPlusBindings ((x, t):xts) es = do
  (xs1, hs1) <- varWeakTermPlus t
  (xs2, hs2) <- varWeakTermPlusBindings xts es
  return (xs1 ++ filter (/= x) xs2, hs1 ++ hs2)

varWeakMeta ::
     (MonadIO m, MonadError String m) => WeakMeta -> m ([Identifier], [Hole])
varWeakMeta (WeakMetaTerminal _) = return ([], [])
varWeakMeta (WeakMetaNonTerminal ref _) = do
  t <- readWeakTermRef ref
  varWeakTermPlus t

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
substWeakMeta sub (WeakMetaNonTerminal ref ml) = do
  t <- readWeakTermRef ref
  t' <- substWeakTermPlus sub t
  writeWeakTermRef ref t'
  return $ WeakMetaNonTerminal ref ml

readWeakTermRef ::
     (MonadIO m, MonadError String m) => WeakTermRef -> m WeakTermPlus
readWeakTermRef (WeakTermRef ref) = do
  mt <- liftIO $ readIORef ref
  case mt of
    Nothing -> throwError "readWeakTermRef for Nothing"
    Just t -> return t

writeWeakTermRef :: (MonadIO m) => WeakTermRef -> WeakTermPlus -> m ()
writeWeakTermRef (WeakTermRef ref) t = liftIO $ writeIORef ref (Just t)

newWeakTermRef :: (MonadIO m) => Maybe WeakTermPlus -> m WeakTermRef
newWeakTermRef mt = do
  ref <- liftIO $ newIORef mt
  return $ WeakTermRef ref

isReducible :: WeakTermPlus -> Bool
isReducible (_, WeakTermTau) = False
isReducible (_, WeakTermTheta _) = False
isReducible (_, WeakTermUpsilon _) = False
isReducible (_, WeakTermPi _ _) = False
isReducible (_, WeakTermPiIntro {}) = False
isReducible (_, WeakTermPiElim (_, WeakTermPiIntro xts _) es)
  | length xts == length es = True
isReducible (_, WeakTermPiElim (_, WeakTermMu _ _) _) = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntS _ _), (_, WeakTermIntS _ _)])
  | Just (LowTypeIntS _, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermIntU _ _), (_, WeakTermIntU _ _)])
  | Just (LowTypeIntU _, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat16 _), (_, WeakTermFloat16 _)])
  | Just (LowTypeFloat FloatSize16, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat32 _), (_, WeakTermFloat32 _)])
  | Just (LowTypeFloat FloatSize32, _) <- asBinaryOpMaybe c = True
isReducible (_, WeakTermPiElim (_, WeakTermTheta c) [(_, WeakTermFloat64 _), (_, WeakTermFloat64 _)])
  | Just (LowTypeFloat FloatSize64, _) <- asBinaryOpMaybe c = True
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
