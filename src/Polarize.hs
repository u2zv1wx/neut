-- This module "polarizes" a neutral term into a negative term. Operationally,
-- this corresponds to determination of the order of evaluation. In proof-theoretic
-- term, we translate a ordinary dependent calculus to a dependent variant of
-- Call-By-Push-Value, although this translation doesn't preserve types when the
-- given term includes dependent sigma-elimination. A detailed explanation of
-- Call-By-Push-Value can be found in P. Levy. "Call-by-Push-Value: A Subsuming
-- Paradigm". Ph. D. thesis, Queen Mary College, 2001.
module Polarize
  ( polarize
  ) where

import           Control.Monad.Except

import           Data.Basic
import           Data.Env
import           Data.Term
import           Data.WeakCode
import           Reduce.WeakCode

polarize :: TermPlus -> WithEnv WeakCodePlus
polarize (m, TermTau) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return (up u ml, WeakCodeUpIntro (self u ml, WeakDataTau))
    _ -> throwError "polarize.tau"
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return (up u ml, WeakCodeUpIntro (self u ml, WeakDataUpsilon x))
    _ -> throwError "polarize.upsilon"
polarize (m, TermEpsilon x) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return (up u ml, WeakCodeUpIntro (self u ml, WeakDataEpsilon x))
    _ -> throwError "polarize.epsilon"
polarize (m, TermEpsilonIntro l) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) ->
      return (up u ml, WeakCodeUpIntro (self u ml, WeakDataEpsilonIntro l))
    _ -> throwError "polarize.epsilon-intro"
polarize (m, TermEpsilonElim (x, t) e bs) = do
  (t1, ml) <- polarizeMeta m
  case t1 of
    (_, WeakCodeUpIntro u) -> do
      let (cs, es) = unzip bs
      es' <- mapM polarize es
      (y, ye) <- polarize' e
      (z, zt) <- polarize' t
      bindLet [ye, zt] (self u ml, WeakCodeEpsilonElim (x, z) y (zip cs es'))
    _ -> throwError "polarize.epsilon-elim"
polarize (m, TermPi xts) = do
  let (xs, ts) = unzip xts
  undefined
  -- (z, zt) <- polarize' t
  -- bindLet
  --   (zt1 : yts' ++ [zt])
  --   ( up z1 ml
  --   , WeakDataUp
  --       ( self z1 ml
  --       , WeakDataDown
  --           (undefined, WeakCodePi (zip xs ys') (fst $ snd zt, WeakDataUp z))))
polarize (m, TermPiIntro xts e) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro d@(_, WeakDataDown n)) -> do
      (ys', yts', xs) <- polarizePlus xts
      e' <- polarize e
      bindLet
        yts'
        ( up d ml
        , WeakCodeUpIntro
            ( self d ml
            , WeakDataDownIntro (self n ml, WeakCodePiIntro (zip xs ys') e')))
    _ -> throwError "polarize.pi-intro"
polarize (m, TermPiElim e@(me, _) es) = do
  (t1, ml1) <- polarizeMeta me
  (t2, ml2) <- polarizeMeta m
  case (t1, t2) of
    ((_, WeakCodeUpIntro (_, WeakDataDown p)), (_, WeakCodeUpIntro t)) -> do
      (f', fe') <- polarize' e
      (xs', xes') <- unzip <$> mapM polarize' es
      bindLet
        (fe' : xes')
        (self t ml2, WeakCodePiElim (self p ml1, WeakCodeDownElim f') xs')
    _ -> throwError "polarize.pi-elim"
polarize (m, TermSigma xts) = do
  (t, ml) <- polarizeMeta m
  (ys', yts', xs) <- polarizePlus xts
  case t of
    (_, WeakCodeUpIntro u) ->
      bindLet
        yts'
        (up u ml, WeakCodeUpIntro (self u ml, WeakDataSigma (zip xs ys')))
    _ -> throwError "polarize.epsilon-intro"
polarize (m, TermSigmaIntro es) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) -> do
      (xs, xes) <- unzip <$> mapM polarize' es
      bindLet xes (up u ml, WeakCodeUpIntro (self u ml, WeakDataSigmaIntro xs))
    _ -> throwError "polarize.sigma-intro"
polarize (m, TermSigmaElim xts e1 e2) = do
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro u) -> do
      (z', ze1') <- polarize' e1
      (ys', yts', xs) <- polarizePlus xts
      e2' <- polarize e2
      bindLet (ze1' : yts') (self u ml, WeakCodeSigmaElim (zip xs ys') z' e2')
    _ -> throwError "polarize.sigma-elim"
polarize (m, TermMu (x, t) e) = do
  (t1, ml) <- polarizeMeta m
  case t1 of
    (_, WeakCodeUpIntro u) -> do
      (y', yt') <- polarize' t
      (k', kt') <- polarize' e
      inner <- bindLet [kt'] (self u ml, WeakCodeDownElim k')
      bindLet [yt'] (self u ml, WeakCodeMu (x, y') inner)
    _ -> throwError "polarize.mu"

polarize' :: TermPlus -> WithEnv (WeakDataPlus, (Identifier, WeakCodePlus))
polarize' e@(m, _) = do
  e' <- polarize e
  (t, ml) <- polarizeMeta m
  case t of
    (_, WeakCodeUpIntro (_, WeakDataUp p)) -> do
      x <- newNameWith "var"
      return ((self p ml, WeakDataUpsilon x), (x, e'))
    _ -> throwError "polarize'"

bindLet :: [(Identifier, WeakCodePlus)] -> WeakCodePlus -> WithEnv WeakCodePlus
bindLet [] cont = return cont
bindLet ((x, e@(m, _)):xes) cont = do
  e' <- bindLet xes cont
  let (typeOfCont, ml) = bar $ fst e'
  let (t2, _) = bar m
  case t2 of
    (_, WeakDataUp d) -> return (self typeOfCont ml, WeakCodeUpElim (x, d) e e')
    _ -> throwError "bindLet"

obtainInfo :: Meta -> (TermPlus, Maybe (Int, Int))
obtainInfo (MetaTerminal ml)      = ((MetaTerminal ml, TermTau), ml)
obtainInfo (MetaNonTerminal t ml) = (t, ml)

bar :: WeakMeta -> (WeakDataPlus, Maybe (Int, Int))
bar (WeakMetaTerminal ml)      = ((WeakMetaTerminal ml, WeakDataTau), ml)
bar (WeakMetaNonTerminal t ml) = (t, ml)

polarizePlus ::
     [(a, TermPlus)]
  -> WithEnv ([WeakDataPlus], [(Identifier, WeakCodePlus)], [a])
polarizePlus xts = do
  let (xs, ts) = unzip xts
  (ys', yts') <- unzip <$> mapM polarize' ts
  return (ys', yts', xs)

polarizeMeta :: Meta -> WithEnv (WeakCodePlus, Maybe (Int, Int))
polarizeMeta m = do
  let (t, ml) = obtainInfo m
  t' <- polarize t >>= reduceWeakCodePlus
  return (t', ml)

self :: WeakDataPlus -> Maybe (Int, Int) -> WeakMeta
self = WeakMetaNonTerminal

up :: WeakDataPlus -> Maybe (Int, Int) -> WeakMeta
up u ml = WeakMetaNonTerminal (WeakMetaTerminal ml, WeakDataUp u) ml

-- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv WeakCodePlus
polarizeTheta _ _ = undefined
-- foo m body = do
--   case m of
--     MetaNonTerminal t ml -> do
--       (z, zt) <- polarize' t
--       let m1 = WeakDataMetaNonTerminal z ml
--       let m2 = WeakCodeMetaNonTerminal (undefined, WeakDataUp z) ml
--       bindLet [zt] body
--     MetaTerminal ml -> do
--       let m1 = WeakDataMetaTerminal ml
--       let empty1 = WeakDataMetaTerminal ml
--       let empty2 = WeakCodeMetaTerminal ml
--       let m2 =
--             WeakCodeMetaNonTerminal
--               (empty2, WeakDataUp (empty1, WeakDataTau))
--               ml
--       return (m2, WeakDataUpIntro (m1, WeakDataTau))
--   -- | Just c <- getPrintConstant x = toPrintDefinition c
--   -- | Just c <- getArithBinOpConstant x = toArithBinOpDefinition c
--   -- | otherwise = return $ WeakDataUpIntro $ WeakDataConst x
-- toArithLowType :: Identifier -> Maybe LowType
-- toArithLowType x
--   | not (null x)
--   , Just y <- readMaybe $ tail x
--   , y > 0 =
--     case head x of
--       'i' -> Just $ LowTypeSignedInt y
--       'u' -> Just $ LowTypeUnsignedInt y
--       'f' -> Just $ LowTypeFloat y
--       _   -> Nothing
--   | otherwise = Nothing
-- getPrintConstant :: Identifier -> Maybe Constant
-- getPrintConstant x = do
--   let xs = wordsWhen (== '.') x
--   if length xs == 3 && head xs == "core" && xs !! 2 == "print"
--     then do
--       lowType <- toArithLowType $ xs !! 1
--       return $ ConstantPrint lowType
--     else Nothing
-- toPrintDefinition :: Constant -> WithEnv WeakCode
-- toPrintDefinition c = do
--   x <- newNameWith "arg"
--   undefined
--   -- makeClosure [x] $ WeakCodeConstElim c [WeakDataUpsilon x]
-- getArithBinOpConstant :: Identifier -> Maybe Constant
-- getArithBinOpConstant x = do
--   let xs = wordsWhen (== '.') x
--   if length xs == 3 && head xs == "core"
--     then do
--       lowType <- toArithLowType $ xs !! 1
--       binOp <- toArithBinOp $ xs !! 2
--       return $ ConstantArith lowType binOp
--     else Nothing
-- toArithBinOp :: Identifier -> Maybe Arith
-- toArithBinOp "add" = Just ArithAdd
-- toArithBinOp "sub" = Just ArithSub
-- toArithBinOp "mul" = Just ArithMul
-- toArithBinOp "div" = Just ArithDiv
-- toArithBinOp _     = Nothing
-- toArithBinOpDefinition :: Constant -> WithEnv WeakCode
-- toArithBinOpDefinition c = do
--   undefined
--   -- x <- newNameWith "arg1"
--   -- y <- newNameWith "arg2"
--   -- lamy <-
--   --   makeClosure [y] $ WeakCodeConstElim c [WeakDataUpsilon x, WeakDataUpsilon y]
--   -- makeClosure [x] lamy
-- wordsWhen :: (Char -> Bool) -> String -> [String]
-- wordsWhen p s =
--   case dropWhile p s of
--     "" -> []
--     s' -> w : wordsWhen p s''
--       where (w, s'') = break p s'
