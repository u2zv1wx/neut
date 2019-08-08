module Elaborate
  ( elaborate
  ) where

import           Control.Comonad.Cofree
import           Control.Monad.Except
import           Control.Monad.State
import           Control.Monad.Trans.Except
import           Data.List                  (nub)
import qualified Data.Map.Strict            as Map
import           Text.Read                  (readMaybe)

import           Data.Basic
import           Data.Constraint
import           Data.Env
import           Data.Term
import           Data.WeakTerm
import           Elaborate.Analyze
import           Elaborate.Infer
import           Elaborate.Synthesize
import           Reduce.Term
import           Reduce.WeakTerm

-- Given a term `e` and its name `main`, this function
--   (1) traces `e` using `infer e`, collecting type constraints,
--   (2) updates typeEnv for `main` by the result of `infer e`,
--   (3) analyze the constraints, solving easy ones,
--   (4) synthesize these analyzed constraints, solving as many solutions as possible,
--   (5) elaborate the given term using the result of synthesis.
-- The inference algorithm in this module is based on L. de Moura, J. Avigad,
-- S. Kong, and C. Roux. "Elaboration in Dependent Type Theory", arxiv,
-- https://arxiv.org/abs/1505.04324, 2015.
elaborate :: WeakTerm -> WithEnv Term
elaborate e = do
  _ <- infer 0 [] e
  -- Kantian type-inference ;)
  gets constraintEnv >>= analyze
  gets constraintQueue >>= synthesize
  -- update the type environment by resulting substitution
  lenv <- gets levelEnv
  sub <- gets substEnv
  tenv <- gets typeEnv
  let tenv' = Map.map (substWeakLevel lenv . substWeakTerm sub) tenv
  modify (\env -> env {typeEnv = tenv'})
  -- use the resulting substitution to elaborate `e`.
  let e' = substWeakTerm sub e
  checkLevelSanity -- check if all the level constraints are satisfied
  exhaust e' >>= elaborate' 0 >>= setupTopLevel

-- This function translates a well-typed term into an untyped term in a
-- reduction-preserving way. Here, we translate types into units (nullary product).
-- This doesn't cause any problem since types doesn't have any beta-reduction.
elaborate' :: Int -> WeakTerm -> WithEnv Term
elaborate' _ (_ :< WeakTermUniv _) = return zero
elaborate' _ (_ :< WeakTermUpsilon x) = return $ TermUpsilon x
elaborate' _ (_ :< WeakTermEpsilon _) = return zero
elaborate' _ (meta :< WeakTermEpsilonIntro x) = do
  t <- lookupTypeEnv' meta
  t' <- reduceWeakTerm t
  case t' of
    _ :< WeakTermEpsilon i -> return $ TermEpsilonIntro x (asLowType i)
    _                      -> lift $ throwE "epsilon"
elaborate' i (_ :< WeakTermEpsilonElim (x, _) e branchList) = do
  e' <- elaborate' i e
  branchList' <-
    forM branchList $ \(l, body) -> do
      body' <- elaborate' i body
      return (l, body')
  return $ TermEpsilonElim x e' branchList'
elaborate' _ (_ :< WeakTermConst x) = return $ TermConst x
elaborate' _ (_ :< WeakTermPi _ _) = return zero
elaborate' i (_ :< WeakTermPiIntro j xts e) = do
  e' <- elaborate' i e
  j' <- elaborateLevel j >>= withOffset
  return $ TermPiIntro j' (map fst xts) e'
elaborate' i (_ :< WeakTermPiElim _ e es) = do
  e' <- elaborate' i e
  es' <- mapM (elaborate' i) es
  return $ TermPiElim e' es'
elaborate' _ (_ :< WeakTermSigma _ _) = return zero
elaborate' i (_ :< WeakTermSigmaIntro j es) = do
  es' <- mapM (elaborate' i) es
  j' <- elaborateLevel j >>= withOffset
  return $ TermSigmaIntro j' es'
elaborate' i (_ :< WeakTermSigmaElim _ xts e1 e2) = do
  e1' <- elaborate' i e1
  e2' <- elaborate' i e2
  return $ TermSigmaElim (map fst xts) e1' e2'
elaborate' _ (_ :< WeakTermTau _ _) = return zero
elaborate' i (_ :< WeakTermTauIntro _ e) = do
  e' <- elaborate' (i + 1) e
  return $ TermTauIntro e'
elaborate' i (_ :< WeakTermTauElim _ e) = do
  e' <- elaborate' (i - 1) e
  return $ TermTauElim e'
elaborate' _ (_ :< WeakTermTheta _) = return zero
elaborate' i (_ :< WeakTermThetaIntro e) = do
  o <- obtainOrigin
  e' <- elaborate' i e
  return $ TermPiIntro LevelInfinity [o] e'
elaborate' i (_ :< WeakTermThetaElim e j) = do
  j' <- elaborateLevel j
  case j' of
    LevelInfinity -> throwError "theta-elim with infinity"
    LevelInt k -> do
      o <- obtainOrigin
      let l = TermConstElim "core.i64.add" [TermUpsilon o, k]
      e' <- elaborate' i e
      return $ TermPiElim e' [l]
elaborate' i (meta :< WeakTermMu (x, t) e) = do
  t' <- reduceWeakTerm t
  let fvs = varWeakTerm $ meta :< WeakTermMu (x, t) e
  e' <- elaborate' i e
  let fvs' = map TermUpsilon fvs
  insTermEnv x fvs $ substTerm [(x, TermConstElim x fvs')] e'
  case t' of
    _ :< WeakTermPi _ _ -> return $ TermConstElim x fvs'
    _ :< WeakTermTheta _ -> return $ TermConstElim x fvs'
    _ ->
      lift $ throwE "CBV recursion is allowed only for Pi-types and Theta-types"
elaborate' i (_ :< WeakTermHole (x, j)) = do
  sub <- gets substEnv
  case lookup x sub of
    Just e  -> elaborate' i $ shiftWeakTerm j e
    Nothing -> lift $ throwE $ "elaborate' i: remaining hole: " ++ x

exhaust :: WeakTerm -> WithEnv WeakTerm
exhaust e = do
  b <- exhaust' e
  if b
    then return e
    else lift $ throwE "non-exhaustive pattern"

elaborateLevel :: WeakLevel -> WithEnv Level
elaborateLevel (WeakLevelInt i) =
  return $ LevelInt (TermEpsilonIntro (LiteralInteger i) (LowTypeSignedInt 64))
elaborateLevel WeakLevelInfinity = return LevelInfinity
elaborateLevel (WeakLevelAdd i1 i2) = do
  i1' <- elaborateLevel i1
  i2' <- elaborateLevel i2
  case (i1', i2') of
    (LevelInt j1, LevelInt j2) ->
      return $ LevelInt $ TermConstElim "core.i64.add" [j1, j2]
    _ -> return LevelInfinity
elaborateLevel (WeakLevelNegate i) = do
  i' <- elaborateLevel i
  case i' of
    LevelInt j -> do
      let z = TermEpsilonIntro (LiteralInteger 0) (LowTypeSignedInt 64)
      return $ LevelInt $ TermConstElim "core.i64.sub" [z, j]
    _ -> throwError "Negating infinity"
elaborateLevel (WeakLevelHole x) = do
  lenv <- gets levelEnv
  case lookup x lenv of
    Just i  -> elaborateLevel i
    Nothing -> throwError $ "Unresolved level hole: " ++ x

withOffset :: Level -> WithEnv Level
withOffset (LevelInt e) = do
  o <- obtainOrigin
  return $ LevelInt $ TermConstElim "core.i64.add" [TermUpsilon o, e]
withOffset LevelInfinity = return LevelInfinity

-- e ~> (lam ORIGIN. e) @ 0
setupTopLevel :: Term -> WithEnv Term
setupTopLevel e = do
  o <- obtainOrigin
  let z = TermEpsilonIntro (LiteralInteger 0) (LowTypeSignedInt 64)
  return $ TermPiElim (TermPiIntro LevelInfinity [o] e) [z]

exhaust' :: WeakTerm -> WithEnv Bool
exhaust' (_ :< WeakTermUniv _) = return True
exhaust' (_ :< WeakTermUpsilon _) = return True
exhaust' (_ :< WeakTermEpsilon _) = return True
exhaust' (_ :< WeakTermEpsilonIntro _) = return True
exhaust' (_ :< WeakTermEpsilonElim (_, t) e1 branchList) = do
  b1 <- exhaust' e1
  let labelList = map fst branchList
  t' <- reduceWeakTerm t
  case t' of
    _ :< WeakTermEpsilon x -> exhaustEpsilonIdentifier x labelList b1
    _                      -> lift $ throwE "type error (exhaust)"
exhaust' (_ :< WeakTermPi _ xts) = allM exhaust' $ map snd xts
exhaust' (_ :< WeakTermPiIntro _ _ e) = exhaust' e
exhaust' (_ :< WeakTermPiElim _ e es) = allM exhaust' $ e : es
exhaust' (_ :< WeakTermSigma _ xts) = allM exhaust' $ map snd xts
exhaust' (_ :< WeakTermSigmaIntro _ es) = allM exhaust' es
exhaust' (_ :< WeakTermSigmaElim _ _ e1 e2) = allM exhaust' [e1, e2]
exhaust' (_ :< WeakTermTau _ t) = exhaust' t
exhaust' (_ :< WeakTermTauIntro _ e) = exhaust' e
exhaust' (_ :< WeakTermTauElim _ e) = exhaust' e
exhaust' (_ :< WeakTermTheta t) = exhaust' t
exhaust' (_ :< WeakTermThetaIntro e) = exhaust' e
exhaust' (_ :< WeakTermThetaElim e _) = exhaust' e
exhaust' (_ :< WeakTermMu _ e) = exhaust' e
exhaust' (_ :< WeakTermConst _) = return True
exhaust' (_ :< WeakTermHole _) = return False

exhaustEpsilonIdentifier :: Identifier -> [Case] -> Bool -> WithEnv Bool
exhaustEpsilonIdentifier x labelList b1 = do
  ienv <- gets indexEnv
  case lookup x ienv of
    Nothing -> undefined -- xはi32とかそのへんのやつ
    Just ls ->
      if length ls <= length (nub labelList)
        then return $ b1 && True
        else return False

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = return True
allM p (x:xs) = do
  b1 <- p x
  b2 <- allM p xs
  return $ b1 && b2

zero :: Term
zero = TermEpsilonIntro (LiteralInteger 0) $ LowTypeSignedInt 64

asLowType :: Identifier -> LowType
asLowType x
  | length x > 1
  , 'i' <- head x
  , Just i <- readMaybe (tail x)
  , 1 <= i
  , i <= 2 ^ (23 :: Int) - 1 = LowTypeSignedInt i
asLowType x
  | length x > 1
  , 'u' <- head x
  , Just i <- readMaybe (tail x)
  , 1 <= i
  , i <= 2 ^ (23 :: Int) - 1 = LowTypeUnsignedInt i
asLowType x
  | length x > 1
  , 'f' <- head x
  , Just i <- readMaybe (tail x)
  , i `elem` [16, 32, 64] = LowTypeFloat i
asLowType _ = LowTypeSignedInt 64 -- sortals are represented as int

checkLevelSanity :: WithEnv ()
checkLevelSanity = do
  cs <- gets levelConstraintEnv
  checkLevelSanity' cs

checkLevelSanity' :: [LevelConstraint] -> WithEnv ()
checkLevelSanity' [] = return ()
checkLevelSanity' (LevelConstraintEQ l1 l2:cs) =
  checkLevelSanity'' (==) l1 l2 cs
checkLevelSanity' (LevelConstraintLE l1 l2:cs) =
  checkLevelSanity'' (<=) l1 l2 cs
checkLevelSanity' (LevelConstraintLEType l1 t:cs) = do
  l2 <- obtainLevel t
  checkLevelSanity'' (<=) l1 l2 cs
checkLevelSanity' (LevelConstraintFinite l:cs) = do
  l' <- elaborateLevel l
  case l' of
    LevelInfinity -> throwError "levelconstraintfinite"
    _             -> checkLevelSanity' cs
checkLevelSanity' (LevelConstraintInfiniteType t:cs) = do
  l <- obtainLevel t >>= elaborateLevel
  case l of
    LevelInfinity -> checkLevelSanity' cs
    _             -> throwError "levelconstraintinfinitetype"

checkLevelSanity'' ::
     (Int -> Int -> Bool)
  -> WeakLevel
  -> WeakLevel
  -> [LevelConstraint]
  -> WithEnv ()
checkLevelSanity'' f l1 l2 cs = do
  l1' <- elaborateLevel l1
  l2' <- elaborateLevel l2
  case (l1', l2') of
    (LevelInfinity, LevelInfinity) -> checkLevelSanity' cs
    (LevelInt e1, LevelInt e2) -> do
      e1' <- reduceTerm e1
      e2' <- reduceTerm e2
      case (e1', e2') of
        (TermEpsilonIntro (LiteralInteger i1) _, TermEpsilonIntro (LiteralInteger i2) _)
          | f i1 i2 -> checkLevelSanity' cs
        _ -> throwError "levelconstrainteq"
    _ -> throwError "levelconstrainteq"

obtainLevel :: WeakTerm -> WithEnv WeakLevel
obtainLevel t = do
  sub <- gets substEnv
  reduceWeakTerm (substWeakTerm sub t) >>= obtainLevel'

obtainLevel' :: WeakTerm -> WithEnv WeakLevel
obtainLevel' t =
  case t of
    _ :< WeakTermUniv l -> do
      l' <- elaborateLevel l
      case l' of
        LevelInfinity -> throwError "obtainLevel.LevelInfinity"
        _             -> return WeakLevelInfinity
    _ :< WeakTermUpsilon x -> do
      u <- lookupTypeEnv' x
      case u of
        _ :< WeakTermUniv l -> return l
        _ -> throwError $ "obtainLevel.WeakTermUpsilon, x = " ++ x
    _ :< WeakTermEpsilon _ -> return WeakLevelInfinity
    _ :< WeakTermPi l _ -> return l
    _ :< WeakTermSigma l _ -> return l
    _ :< WeakTermTau _ t' -> obtainLevel t'
    _ :< WeakTermTheta _ -> return WeakLevelInfinity
    _ -> throwError "obtainLevel"
