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
  (t, ml) <- polarizeMeta' m
  case t of
    n@(_, WeakCodeUp p) ->
      return (negSelf n ml, WeakCodeUp (posSelf p ml, WeakDataTau))
    _ -> throwError "polarize.tau"
polarize (m, TermTheta x) = polarizeTheta m x
polarize (m, TermUpsilon x) = do
  (t, ml) <- polarizeMeta' m
  case t of
    u@(_, WeakCodeUp d@(_, WeakDataTau))
     -- type variable: x ~> ↑x
     -> return (negSelf u ml, WeakCodeUp (posSelf d ml, WeakDataUpsilon x))
    u@(_, WeakCodeUp d)
     -- ordinary variable: x ~> return x
     -> return (negSelf u ml, WeakCodeUpIntro (posSelf d ml, WeakDataUpsilon x))
    _ -> throwError "polarize.upsilon"
polarize (m, TermEpsilon x) = do
  (t, ml) <- polarizeMeta' m
  case t of
    u@(_, WeakCodeUp d) ->
      return (negSelf u ml, WeakCodeUp (posSelf d ml, WeakDataEpsilon x))
    _ -> throwError "polarize.epsilon"
polarize (m, TermEpsilonIntro l) = do
  (t, ml) <- polarizeMeta' m
  case t of
    u@(_, WeakCodeUp d) ->
      return
        (negSelf u ml, WeakCodeUpIntro (posSelf d ml, WeakDataEpsilonIntro l))
    _ -> throwError "polarize.epsilon-intro"
polarize (m, TermEpsilonElim (x, t) e bs) = do
  (t1, ml) <- polarizeMeta' m
  let (cs, es) = unzip bs
  es' <- mapM polarize es
  (y, ye) <- polarize' e
  (z, zt) <- polarize' t
  bindLet [ye, zt] (negSelf t1 ml, WeakCodeEpsilonElim (x, z) y (zip cs es'))
polarize (m, TermPi xts t) = do
  (z1, zt1, ml) <- polarizeMeta m
  (ys', yts', xs) <- polarizePlus xts
  (z, zt) <- polarize' t
  bindLet
    (zt1 : yts' ++ [zt]) -- zt1はup-introじゃなくupかもしれないのでbindはできないのでは…？
    ( up z1 ml
    , WeakCodeUp
        ( posSelf z1 ml
        , WeakDataDown
            (negUniv ml, WeakCodePi (zip xs ys') (fst $ snd zt, WeakCodeUp z))))
polarize (m, TermPiIntro xts e) = do
  (t1, ml) <- polarizeMeta' m
  case t1 of
    u@(_, WeakCodeUp d@(_, WeakDataDown p)) -> do
      (ys', yts', xs) <- polarizePlus xts
      e' <- polarize e
      bindLet
        yts'
        ( negSelf u ml
        , WeakCodeUpIntro
            ( posSelf d ml
            , WeakDataDownIntro (negSelf p ml, WeakCodePiIntro (zip xs ys') e')))
    _ -> throwError "polarize.pi-intro"
polarize (m, TermPiElim e@(me, _) es) = do
  (t1, ml1) <- polarizeMeta' me
  case t1 of
    (_, WeakCodeUp (_, WeakDataDown p@(_, WeakCodePi _ _))) -> do
      (n, ml) <- polarizeMeta' m
      (f', fe') <- polarize' e
      (xs', xes') <- unzip <$> mapM polarize' es
      bindLet
        (fe' : xes')
        (negSelf n ml, WeakCodePiElim (negSelf p ml1, WeakCodeDownElim f') xs')
    _ -> throwError "polarize.pi-elim"
polarize (m, TermSigma xts) = do
  (t, ml) <- polarizeMeta' m
  -- (z1, zt1, ml) <- polarizeMeta m
  (ys', yts', xs) <- polarizePlus xts
  case t of
    u@(_, WeakCodeUp d) ->
      bindLet
        yts'
        ( negSelf u ml
        , WeakCodeUpIntro (posSelf d ml, WeakDataSigma (zip xs ys')))
    _ -> throwError "polarize.epsilon-intro"
  -- (z1, zt1, ml) <- polarizeMeta m
  -- (ys', yts', xs) <- polarizePlus xts
  -- bindLet
  --   (zt1 : yts')
  --   (up z1 ml, WeakCodeUpIntro (posSelf z1 ml, WeakDataSigma (zip xs ys')))
polarize (m, TermSigmaIntro es) = do
  (z1, zt1, ml) <- polarizeMeta m
  (xs, xes) <- unzip <$> mapM polarize' es
  bindLet
    (zt1 : xes)
    (up z1 ml, WeakCodeUpIntro (posSelf z1 ml, WeakDataSigmaIntro xs))
polarize (m, TermSigmaElim xts e1 e2) = do
  (z1, zt1, ml) <- polarizeMeta m
  (z', ze1') <- polarize' e1
  (ys', yts', xs) <- polarizePlus xts
  e2' <- polarize e2
  bindLet (zt1 : ze1' : yts') (up z1 ml, WeakCodeSigmaElim (zip xs ys') z' e2')
polarize (m, TermMu (x, t) e) = do
  (t1, ml) <- polarizeMeta' m
  (y', yt') <- polarize' t
  (k', kt') <- polarize' e
  inner <- bindLet [kt'] (negSelf t1 ml, WeakCodeDownElim k')
  bindLet [yt'] (negSelf t1 ml, WeakCodeMu (x, y') inner)

polarize' :: TermPlus -> WithEnv (WeakDataPlus, (Identifier, WeakCodePlus))
polarize' e@(m, _) = do
  e' <- polarize e
  (t, ml) <- polarizeMeta' m
  case t of
    (_, WeakCodeUp d) -> do
      x <- newNameWith "var"
      return ((posSelf d ml, WeakDataUpsilon x), (x, e'))
    _ -> throwError "polarize'"

bindLet :: [(Identifier, WeakCodePlus)] -> WeakCodePlus -> WithEnv WeakCodePlus
bindLet [] cont = return cont
bindLet ((x, e@(m, _)):xes) cont = do
  e' <- bindLet xes cont
  let (typeOfCont, ml) = bar $ fst e'
  let (t2, _) = bar m
  t2' <- reduceWeakCodePlus t2
  case t2' of
    (_, WeakCodeUp d) -> do
      let t = (WeakCodeMetaTerminal ml, WeakCodeUpElim (x, d) e typeOfCont)
      return (negSelf t ml, WeakCodeUpElim (x, d) e e')
    _ -> throwError "bindLet"

obtainInfo :: Meta -> (TermPlus, Maybe (Int, Int))
obtainInfo (MetaTerminal ml)      = ((MetaTerminal ml, TermTau), ml)
obtainInfo (MetaNonTerminal t ml) = (t, ml)

bar :: WeakCodeMeta -> (WeakCodePlus, Maybe (Int, Int))
bar (WeakCodeMetaTerminal ml) = ((WeakCodeMetaTerminal ml, WeakCodeTau), ml)
bar (WeakCodeMetaNonTerminal t ml) = (t, ml)

polarizePlus ::
     [(a, TermPlus)]
  -> WithEnv ([WeakDataPlus], [(Identifier, WeakCodePlus)], [a])
polarizePlus xts = do
  let (xs, ts) = unzip xts
  (ys', yts') <- unzip <$> mapM polarize' ts
  return (ys', yts', xs)

polarizeMeta ::
     Meta
  -> WithEnv (WeakDataPlus, (Identifier, WeakCodePlus), Maybe (Int, Int))
polarizeMeta m = do
  let (t, ml) = obtainInfo m
  (z, zt) <- polarize' t
  return (z, zt, ml)

polarizeMeta' :: Meta -> WithEnv (WeakCodePlus, Maybe (Int, Int))
polarizeMeta' m = do
  let (t, ml) = obtainInfo m
  t' <- polarize t >>= reduceWeakCodePlus
  return (t', ml)

posSelf :: WeakDataPlus -> Maybe (Int, Int) -> WeakDataMeta
posSelf = WeakDataMetaNonTerminal

negSelf :: WeakCodePlus -> Maybe (Int, Int) -> WeakCodeMeta
negSelf = WeakCodeMetaNonTerminal

up :: WeakDataPlus -> Maybe (Int, Int) -> WeakCodeMeta
up z ml = WeakCodeMetaNonTerminal (WeakCodeMetaTerminal ml, WeakCodeUp z) ml

negUniv :: Maybe (Int, Int) -> WeakCodeMeta
negUniv = WeakCodeMetaTerminal

-- expand definitions of constants
polarizeTheta :: Meta -> Identifier -> WithEnv WeakCodePlus
polarizeTheta _ _ = undefined
-- foo m body = do
--   case m of
--     MetaNonTerminal t ml -> do
--       (z, zt) <- polarize' t
--       let m1 = WeakDataMetaNonTerminal z ml
--       let m2 = WeakCodeMetaNonTerminal (undefined, WeakCodeUp z) ml
--       bindLet [zt] body
--     MetaTerminal ml -> do
--       let m1 = WeakDataMetaTerminal ml
--       let empty1 = WeakDataMetaTerminal ml
--       let empty2 = WeakCodeMetaTerminal ml
--       let m2 =
--             WeakCodeMetaNonTerminal
--               (empty2, WeakCodeUp (empty1, WeakDataTau))
--               ml
--       return (m2, WeakCodeUpIntro (m1, WeakDataTau))
--   -- | Just c <- getPrintConstant x = toPrintDefinition c
--   -- | Just c <- getArithBinOpConstant x = toArithBinOpDefinition c
--   -- | otherwise = return $ WeakCodeUpIntro $ WeakDataConst x
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
