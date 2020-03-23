{-# LANGUAGE OverloadedStrings #-}

module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , interpretIter
  , interpretEnumItem
  , adjustPhase
  , raiseSyntaxError
  , toIdentPlus
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits ((.&.), shiftR)
import Data.Char (ord)
import Data.List (elemIndex, sortOn)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Word (Word8)
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm

interpret :: TreePlus -> WithEnv WeakTermPlus
--
-- foundational interpretations
--
interpret (m, TreeLeaf "tau") = do
  m' <- adjustPhase m
  l <- newCount
  return (m', WeakTermTau l)
interpret (m, TreeNode ((_, TreeLeaf "upsilon"):rest))
  | [(_, TreeLeaf x)] <- rest = do
    m' <- adjustPhase m
    return (m', WeakTermUpsilon $ asIdent x)
  | otherwise = raiseSyntaxError m "(upsilon TREE)"
interpret (m, TreeNode ((_, TreeLeaf "pi"):rest))
  | [(_, TreeNode xts), t] <- rest = do
    (xts', t') <- interpretBinder xts t
    mls <- piUnivLevelsfrom xts' t'
    m' <- adjustPhase m
    return (m', WeakTermPi mls xts' t')
  | otherwise = raiseSyntaxError m "(pi (TREE*) TREE)"
interpret (m, TreeNode ((_, TreeLeaf "pi-introduction"):rest))
  | [(_, TreeNode xts), e] <- rest = do
    (xts', e') <- interpretBinder xts e
    m' <- adjustPhase m
    return (m', WeakTermPiIntro xts' e')
  | otherwise = raiseSyntaxError m "(pi-introduction (TREE*) TREE)"
interpret (m, TreeNode ((_, TreeLeaf "pi-elimination"):rest))
  | e:es <- rest = do
    m' <- adjustPhase m
    interpretPiElim m' e es
  | otherwise = raiseSyntaxError m "(pi-elimination TREE TREE*)" -- e' <- interpret e
interpret (m, TreeNode ((_, TreeLeaf "sigma"):rest))
  | [(_, TreeNode xts), t] <- rest = do
    xts' <- mapM interpretIdentifierPlus xts
    t' <- interpret t
    placeholder <- newNameWith' "cod"
    m' <- adjustPhase m
    return (m', WeakTermSigma $ xts' ++ [(fst t', placeholder, t')])
  | otherwise = raiseSyntaxError m "(sigma (TREE*) TREE)"
interpret (m, TreeNode ((_, TreeLeaf "sigma-introduction"):es)) = do
  m' <- adjustPhase m
  h <- newHole m'
  es' <- mapM interpret es
  return (m', WeakTermSigmaIntro h es')
interpret (m, TreeNode ((_, TreeLeaf "sigma-elimination"):rest))
  | [(_, TreeNode xts), e1, e2] <- rest = do
    xts' <- mapM interpretIdentifierPlus xts
    e1' <- interpret e1
    e2' <- interpret e2
    m' <- adjustPhase m
    h <- newHole m'
    return (m', WeakTermSigmaElim h xts' e1' e2')
  | otherwise = raiseSyntaxError m "(sigma-elimination (TREE*) TREE TREE)"
interpret (m, TreeNode ((_, TreeLeaf "iterate"):rest))
  | [xt, xts@(_, TreeNode _), e] <- rest = do
    (m', xt', xts', e') <- interpretIter (m, TreeNode [xt, xts, e])
    return (m', WeakTermIter xt' xts' e')
  | otherwise = raiseSyntaxError m "(iterate TREE (TREE*) TREE)"
interpret (m, TreeNode ((_, TreeLeaf "zeta"):rest))
  | [x@(_, TreeLeaf _)] <- rest = do
    (_, x') <- interpretLeaf x
    m' <- adjustPhase m
    let m'' = m' {metaIsAppropriateAsCompletionCandidate = False}
    return (m'', WeakTermZeta x')
  | otherwise = raiseSyntaxError m "(zeta LEAF)"
interpret (m, TreeNode ((_, TreeLeaf "constant"):rest))
  | [(_, TreeLeaf x)] <- rest = do
    m' <- adjustPhase m
    return (m', WeakTermConst $ asIdent x)
  | otherwise = raiseSyntaxError m "(constant LEAF)"
interpret (m, TreeNode ((_, TreeLeaf "f16"):rest))
  | [(mx, TreeLeaf x)] <- rest = do
    case readMaybe $ T.unpack x of
      Nothing -> raiseError mx "the argument of `f16` must be a float"
      Just x' -> do
        m' <- adjustPhase m
        return (m', WeakTermFloat16 x')
  | otherwise = raiseSyntaxError m "(f16 LEAF)"
interpret (m, TreeNode ((_, TreeLeaf "f32"):rest))
  | [(mx, TreeLeaf x)] <- rest = do
    case readMaybe $ T.unpack x of
      Nothing -> raiseError mx "the argument of `f32` must be a float"
      Just x' -> do
        m' <- adjustPhase m
        return (m', WeakTermFloat32 x')
  | otherwise = raiseSyntaxError m "(f32 LEAF)"
interpret (m, TreeNode ((_, TreeLeaf "f64"):rest))
  | [(mx, TreeLeaf x)] <- rest = do
    case readMaybe $ T.unpack x of
      Nothing -> raiseError mx "the argument of `f64` must be a float"
      Just x' -> do
        m' <- adjustPhase m
        return (m', WeakTermFloat64 x')
  | otherwise = raiseSyntaxError m "(f64 LEAF)"
interpret (m, TreeNode ((_, TreeLeaf "enum"):rest))
  | [(_, TreeLeaf x)] <- rest = do
    m' <- adjustPhase m
    case (readEnumTypeIntS x, readEnumTypeIntU x) of
      (Just i, _) -> return (m', WeakTermEnum $ EnumTypeIntS i)
      (_, Just i) -> return (m', WeakTermEnum $ EnumTypeIntU i)
      _ -> return (m', WeakTermEnum $ EnumTypeLabel x)
  | otherwise = raiseSyntaxError m "(enum LEAF)"
interpret (m, TreeNode ((_, TreeLeaf "enum-introduction"):rest))
  | [l] <- rest = do
    l' <- interpretEnumValue l
    m' <- adjustPhase m
    return (m', WeakTermEnumIntro l')
  | otherwise = raiseSyntaxError m "(enum-introduction TREE)"
interpret (m, TreeNode ((_, TreeLeaf "enum-elimination"):rest))
  | e:cs <- rest = do
    e' <- interpret e
    cs' <- mapM interpretClause cs
    m' <- adjustPhase m
    h <- newHole m'
    return (m', WeakTermEnumElim (e', h) cs')
  | otherwise = raiseSyntaxError m "(enum-elimination TREE TREE*)"
interpret (m, TreeNode ((_, TreeLeaf "array"):rest))
  | [dom, kind] <- rest = do
    dom' <- interpret dom
    kind' <- asArrayKind kind
    m' <- adjustPhase m
    return (m', WeakTermArray dom' kind')
  | otherwise = raiseSyntaxError m "(array TREE TREE)"
interpret (m, TreeNode ((_, TreeLeaf "array-introduction"):rest))
  | kind:es <- rest = do
    kind' <- asArrayKind kind
    es' <- mapM interpret es
    m' <- adjustPhase m
    return (m', WeakTermArrayIntro kind' es')
  | otherwise = raiseSyntaxError m "(array-introduction TREE TREE*)"
interpret (m, TreeNode ((_, TreeLeaf "array-elimination"):rest))
  | [kind, (_, TreeNode xts), e1, e2] <- rest = do
    kind' <- asArrayKind kind
    e1' <- interpret e1
    (xts', e2') <- interpretBinder xts e2
    m' <- adjustPhase m
    return (m', WeakTermArrayElim kind' xts' e1' e2')
  | otherwise = raiseSyntaxError m "(array-elimination TREE (TREE*) TREE TREE)"
interpret (m, TreeNode ((_, TreeLeaf "struct"):ks)) = do
  ks' <- mapM asArrayKind ks
  m' <- adjustPhase m
  return (m', WeakTermStruct ks')
interpret (m, TreeNode ((_, TreeLeaf "struct-introduction"):ets)) = do
  ets' <- mapM interpretStructIntro ets
  m' <- adjustPhase m
  return (m', WeakTermStructIntro ets')
interpret (m, TreeNode ((_, TreeLeaf "struct-elimination"):rest))
  | [(_, TreeNode xts), e1, e2] <- rest = do
    e1' <- interpret e1
    xts' <- mapM interpretStructElim xts
    e2' <- interpret e2
    m' <- adjustPhase m
    return (m', WeakTermStructElim xts' e1' e2')
  | otherwise = raiseSyntaxError m "(struct-elimination (TREE*) TREE TREE)"
interpret (m, TreeNode ((_, TreeLeaf "case"):rest))
  | e:cxtes <- rest = do
    e' <- interpret e
    cxtes' <- mapM interpretCaseClause cxtes
    m' <- adjustPhase m
    h <- newHole m'
    return (m', WeakTermCase (e', h) cxtes')
  | otherwise = raiseSyntaxError m "(case TREE TREE*)"
-- A -> FνF -> νF (i.e. copattern matching (although I think it's more correct to say "record" or something like that,
-- considering that the constructed term using `FνF -> νF` is just a record after all))
interpret (m, TreeNode ((_, TreeLeaf "cocase"):rest))
  | codType:cocaseClauseList <- rest = do
    (a, args) <- interpretCoinductive codType
    m' <- adjustPhase m
    cocaseClauseList' <- mapM interpretCocaseClause cocaseClauseList
    let codType' = (m, WeakTermPiElim (m, WeakTermUpsilon a) args)
    es <- cocaseAsSigmaIntro m a codType' cocaseClauseList'
    return (m', WeakTermSigmaIntro codType' es)
  | otherwise = raiseSyntaxError m "(cocase TREE TREE*)"
--
-- auxiliary interpretations
--
interpret (m, TreeNode ((_, TreeLeaf "product"):ts)) = do
  ts' <- mapM interpret ts
  let ms = map fst ts'
  xs <- mapM (const $ newNameWith' "sig") ts'
  m' <- adjustPhase m
  return (m', WeakTermSigma (zip3 ms xs ts'))
interpret (m, TreeNode ((_, TreeLeaf "record"):rest))
  | codType:clauseList <- rest = do
    (a, args) <- interpretCoinductive codType
    m' <- adjustPhase m
    clauseList' <- mapM interpretCocaseClause' clauseList
    let codType' = (m, WeakTermPiElim (m, WeakTermUpsilon a) args)
    es <- cocaseAsSigmaIntro m a codType' [((a, args), clauseList')]
    return (m', WeakTermSigmaIntro codType' es)
  | otherwise = raiseSyntaxError m "(record TREE TREE*)"
interpret (m, TreeLeaf x)
  | Just x' <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    h <- newHole m'
    return (m', WeakTermInt h x')
  | Just x' <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    h <- newHole m'
    return (m', WeakTermFloat h x')
  | Just i <- readEnumTypeIntS x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeIntS i)
  | Just i <- readEnumTypeIntU x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeIntU i)
  | Just str <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    u8s <- forM (encode str) $ \u -> return (m', toValueIntU 8 (toInteger u))
    return (m', WeakTermArrayIntro (ArrayKindIntU 8) u8s) -- parse string as utf-8 encoded u8 array
  | otherwise = do
    m' <- adjustPhase m
    -- Note that enums/constants are interpreted as variables at this stage.
    -- Those are reinterpreted into constants in Rename.
    -- This is to handle terms like `lam (i64 : bool). e` (i.e. bound variable
    -- with the same name of a constant) in saner way.
    return (m', WeakTermUpsilon $ asIdent x)
interpret t@(m, TreeNode es) = do
  m' <- adjustPhase m
  ml <- interpretEnumValueMaybe t
  case (ml, es) of
    (Just l, _) -> return (m', WeakTermEnumIntro l)
    (_, []) -> raiseSyntaxError (fst t) "(TREE TREE*)"
    (_, f:args) -> interpretPiElim m' f args
interpret (m, TreeNodeSquare _) = raiseSyntaxError m "LEAF | TREE"

interpretPiElim :: Meta -> TreePlus -> [TreePlus] -> WithEnv WeakTermPlus
interpretPiElim m f args = do
  (args', headerList) <- unzip <$> mapM interpretBorrow args
  f' <- interpret f
  return $ applyHeader headerList (m, WeakTermPiElim f' args')

applyHeader :: [WeakTermPlus -> WeakTermPlus] -> WeakTermPlus -> WeakTermPlus
applyHeader [] e = e
applyHeader (f:fs) e = f (applyHeader fs e)

-- (e e1 ... en)みたいなやつのei部分をチェックしてborrow成分を集める
interpretBorrow ::
     TreePlus -> WithEnv (WeakTermPlus, WeakTermPlus -> WeakTermPlus)
interpretBorrow (m, TreeNode (f:args))
  | (mmxs, args') <- unzip $ map interpretBorrow' args
  , mxs <- catMaybes mmxs
  , not (null mxs) = do
    f' <- interpret f
    args'' <- mapM interpret args'
    tmp <- newNameWith'' "borrow"
    xts <- mapM toIdentPlus $ mxs ++ [(m, tmp)]
    h <- newHole m
    let app = (m, WeakTermPiElim f' args'')
    return
      ((m, WeakTermUpsilon tmp), \term -> (m, WeakTermSigmaElim h xts app term))
interpretBorrow e = do
  e' <- interpret e
  return (e', id)

interpretBorrow' :: TreePlus -> (Maybe (Meta, Identifier), TreePlus)
interpretBorrow' (m, TreeLeaf s)
  | T.length s > 1
  , T.head s == '&' = (Just (m, asIdent $ T.tail s), (m, TreeLeaf $ T.tail s))
interpretBorrow' t = (Nothing, t)

toIdentPlus :: (Meta, Identifier) -> WithEnv IdentifierPlus
toIdentPlus (m, x) = do
  h <- newHole m
  return (m, x, h)

interpretIdentifierPlus :: TreePlus -> WithEnv IdentifierPlus
interpretIdentifierPlus (m, TreeLeaf x) = do
  (m', x') <- interpretLeaf (m, TreeLeaf x)
  h <- newHole m'
  return (m', x', h)
interpretIdentifierPlus (_, TreeNode [x, t]) = do
  (m', x') <- interpretLeaf x
  t' <- interpret t
  return (m', x', t')
interpretIdentifierPlus t = raiseSyntaxError (fst t) "(LEAF TREE)"

interpretIter :: TreePlus -> WithEnv Def
interpretIter (m, TreeNode [xt, (_, TreeNode xts), e]) = do
  xt' <- interpretIdentifierPlus xt
  (xts', e') <- interpretBinder xts e
  m' <- adjustPhase m
  return (m', xt', xts', e')
interpretIter t = raiseSyntaxError (fst t) "(TREE (TREE ... TREE) TREE)"

interpretLeaf :: TreePlus -> WithEnv (Meta, Identifier)
interpretLeaf (m, TreeLeaf "_") = do
  m' <- adjustPhase m
  let m'' = m' {metaIsAppropriateAsCompletionCandidate = False}
  h <- newNameWith'' "H"
  return (m'', h)
interpretLeaf (m, TreeLeaf x) = do
  m' <- adjustPhase m
  return (m', asIdent x)
interpretLeaf t = raiseSyntaxError (fst t) "LEAF"

interpretEnumValueMaybe :: TreePlus -> WithEnv (Maybe EnumValue)
interpretEnumValueMaybe t =
  (Just <$> interpretEnumValue t) `catchError` (const $ return Nothing)

interpretEnumValue :: TreePlus -> WithEnv EnumValue
interpretEnumValue (m, TreeLeaf x) = do
  b <- isDefinedEnumValue x
  if b
    then return $ EnumValueLabel x
    else raiseError m $ "no such enum-value is defined: " <> x
interpretEnumValue e@(m, TreeNode [(_, TreeLeaf t), (_, TreeLeaf x)]) = do
  let mv1 = readEnumValueIntS t x
  let mv2 = readEnumValueIntU t x
  case (mv1, mv2) of
    (Just v@(EnumValueIntS size x'), _) ->
      if (-1) * (2 ^ (size - 1)) <= x' && x' < 2 ^ size
        then return v
        else raiseError m $
             "the signed integer " <>
             T.pack (show x') <>
             " is supposed to be of type i" <>
             T.pack (show size) <>
             ", but is out of range of i" <> T.pack (show size)
    (_, Just v@(EnumValueIntU size x')) ->
      if 0 <= x' && x' < 2 ^ size
        then return v
        else raiseError m $
             "the unsigned integer " <>
             T.pack (show x') <>
             " is supposed to be of type u" <>
             T.pack (show size) <>
             ", but is out of range of u" <> T.pack (show size)
    _ -> raiseSyntaxError (fst e) "(SINT-TYPE INT) | (UINT-TYPE INT)"
interpretEnumValue t = raiseSyntaxError (fst t) "LEAF | (LEAF LEAF)"

interpretBinder ::
     [TreePlus] -> TreePlus -> WithEnv ([IdentifierPlus], WeakTermPlus)
interpretBinder xts t = do
  xts' <- mapM interpretIdentifierPlus xts
  t' <- interpret t
  return (xts', t')

interpretWeakCase :: TreePlus -> WithEnv WeakCase
--
-- foundational
--
interpretWeakCase (_, TreeNode [(_, TreeLeaf "enum-introduction"), l]) = do
  weakenEnumValue <$> interpretEnumValue l
interpretWeakCase (_, TreeLeaf "default") = return WeakCaseDefault
--
-- auxiliary
--
interpretWeakCase c
  | (m, TreeLeaf i) <- c
  , Just i' <- readMaybe $ T.unpack i = do
    h <- newHole m
    return $ WeakCaseInt h i'
  | otherwise = weakenEnumValue <$> interpretEnumValue c

interpretClause :: TreePlus -> WithEnv (WeakCase, WeakTermPlus)
interpretClause (_, TreeNode [c, e]) = do
  c' <- interpretWeakCase c
  e' <- interpret e
  return (c', e')
interpretClause e = raiseSyntaxError (fst e) "(TREE TREE)"

interpretStructIntro :: TreePlus -> WithEnv (WeakTermPlus, ArrayKind)
interpretStructIntro (_, TreeNode [e, k]) = do
  e' <- interpret e
  k' <- asArrayKind k
  return (e', k')
interpretStructIntro e = raiseSyntaxError (fst e) "(TREE TREE)"

interpretStructElim :: TreePlus -> WithEnv (Meta, Identifier, ArrayKind)
interpretStructElim (_, TreeNode [(m, TreeLeaf x), k]) = do
  k' <- asArrayKind k
  return (m, asIdent x, k')
interpretStructElim e = raiseSyntaxError (fst e) "(LEAF TREE)"

interpretCaseClause ::
     TreePlus -> WithEnv ((Identifier, [IdentifierPlus]), WeakTermPlus)
interpretCaseClause (_, TreeNode [(_, TreeNode ((_, TreeLeaf c):xts)), e]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e' <- interpret e
  return ((asIdent c, xts'), e')
interpretCaseClause t = raiseSyntaxError (fst t) "((LEAF TREE ... TREE) TREE)"

type CocaseClause = ((Identifier, [WeakTermPlus]), [(Identifier, WeakTermPlus)])

-- (cocase (a e ... e)
--   ((a e ... e)
--    (b e)
--    ...
--    (b e))
--   ((a e ... e)
--    (b e)
--    ...
--    (b e)))
interpretCoinductive :: TreePlus -> WithEnv (Identifier, [WeakTermPlus])
interpretCoinductive (_, TreeNode ((_, TreeLeaf c):args)) = do
  args' <- mapM interpret args
  return (asIdent c, args')
interpretCoinductive t = raiseSyntaxError (fst t) "(LEAF TREE ... TREE)"

interpretCocaseClause :: TreePlus -> WithEnv CocaseClause
interpretCocaseClause (_, TreeNode (coind:clauseList)) = do
  (c, args) <- interpretCoinductive coind
  clauseList' <- mapM interpretCocaseClause' clauseList
  return ((c, args), clauseList')
interpretCocaseClause t =
  raiseSyntaxError (fst t) "((LEAF TREE ... TREE) (LEAF TREE) ... (LEAF TREE))"

interpretCocaseClause' :: TreePlus -> WithEnv (Identifier, WeakTermPlus)
interpretCocaseClause' (_, TreeNode [(_, TreeLeaf label), body]) = do
  body' <- interpret body
  return (asIdent label, body')
interpretCocaseClause' t = raiseSyntaxError (fst t) "(LEAF TREE)"

cocaseAsSigmaIntro ::
     Meta
  -> Identifier
  -> WeakTermPlus
  -> [CocaseClause]
  -> WithEnv [WeakTermPlus]
cocaseAsSigmaIntro m (I (name, _)) codType cocaseClauseList = do
  let aes = map (headNameOf m) cocaseClauseList
  bes <- asLamClauseList m cocaseClauseList
  lenv <- gets labelEnv
  case Map.lookup name lenv of
    Nothing -> raiseError m $ "no such coinductive type defined: " <> name
    Just labelList -> do
      iesjes <- labelToIndex m labelList $ aes ++ bes
      let isLinear = linearCheck $ map fst iesjes
      let isExhaustive = length iesjes == length labelList
      case (isLinear, isExhaustive) of
        (False, _) -> raiseError m $ "found a non-linear copattern"
        (_, False) -> raiseError m $ "found a non-exhaustive copattern"
        (True, True) ->
          return $ (map snd $ sortOn fst iesjes) ++ [cocaseBaseValue m codType]

labelToIndex :: Meta -> [T.Text] -> [(Identifier, a)] -> WithEnv [(Int, a)]
labelToIndex _ _ [] = return []
labelToIndex m lenv ((x, e):xes) =
  case elemIndex (asText x) lenv of
    Nothing -> raiseError m $ "no such destructor defined: " <> asText x
    Just i -> do
      ies <- labelToIndex m lenv xes
      return $ (i, e) : ies

asLamClauseList ::
     Meta -> [CocaseClause] -> WithEnv [(Identifier, WeakTermPlus)]
asLamClauseList m cocaseClauseList = do
  fmap concat $
    forM cocaseClauseList $ \((a', args), clauseList) -> do
      let t = (m, WeakTermPiElim (m, WeakTermUpsilon a') args)
      forM clauseList $ \(b, body) -> asLamClause b m t body

asLamClause ::
     Identifier
  -> Meta
  -> WeakTermPlus
  -> WeakTermPlus
  -> WithEnv (Identifier, WeakTermPlus)
asLamClause b m t body = do
  h <- newNameWith' "hole"
  return (b, (m, WeakTermPiIntro [(m, h, t)] body))

headNameOf :: Meta -> CocaseClause -> (Identifier, WeakTermPlus)
headNameOf m ((a, _), _) = (a, (m, WeakTermUpsilon a))

cocaseBaseValue :: Meta -> WeakTermPlus -> WeakTermPlus
cocaseBaseValue m codType =
  ( m
  , WeakTermPiElim
      (m, WeakTermUpsilon $ asIdent "unsafe-cast")
      [ (m, WeakTermPi [] [] (m, WeakTermEnum (EnumTypeIntS 64)))
      , codType
      , (m, (WeakTermPiIntro [] (m, WeakTermEnumIntro (EnumValueIntS 64 0))))
      ])

interpretEnumItem :: Meta -> [TreePlus] -> WithEnv [(T.Text, Int)]
interpretEnumItem m ts = do
  xis <- interpretEnumItem' $ reverse ts
  if linearCheck (map snd xis)
    then return $ reverse xis
    else raiseError m "found a collision of discriminant"

interpretEnumItem' :: [TreePlus] -> WithEnv [(T.Text, Int)]
interpretEnumItem' [] = return []
interpretEnumItem' [t] = do
  (s, mj) <- interpretEnumItem'' t
  return [(s, fromMaybe 0 mj)]
interpretEnumItem' (t:ts) = do
  ts' <- interpretEnumItem' ts
  (s, mj) <- interpretEnumItem'' t
  return $ (s, fromMaybe (1 + headDiscriminantOf ts') mj) : ts'

interpretEnumItem'' :: TreePlus -> WithEnv (T.Text, Maybe Int)
interpretEnumItem'' (_, TreeLeaf s) = return (s, Nothing)
interpretEnumItem'' (_, TreeNode [(_, TreeLeaf s), (_, TreeLeaf i)])
  | Just i' <- readMaybe $ T.unpack i = return (s, Just i')
interpretEnumItem'' t = raiseSyntaxError (fst t) "LEAF | (LEAF LEAF)"

headDiscriminantOf :: [(T.Text, Int)] -> Int
headDiscriminantOf [] = 0
headDiscriminantOf ((_, i):_) = i

readEnumType :: Char -> T.Text -> Int -> (Maybe Int)
readEnumType c str k -- n1, n2, ..., n{i}, ..., n{2^64}
  | T.length str >= 2
  , T.head str == c
  , Just i <- (readMaybe $ T.unpack $ T.tail str :: Maybe Int)
  , 1 <= toInteger i && toInteger i <= 2 ^ k = Just i
readEnumType _ _ _ = Nothing

readEnumTypeIntS :: T.Text -> (Maybe Int)
readEnumTypeIntS str = readEnumType 'i' str 23

readEnumTypeIntU :: T.Text -> (Maybe Int)
readEnumTypeIntU str = readEnumType 'u' str 23

readEnumValueIntS :: T.Text -> T.Text -> Maybe EnumValue
readEnumValueIntS t x
  | Just (LowTypeIntS i) <- asLowTypeMaybe t
  , Just x' <- readMaybe $ T.unpack x = Just $ EnumValueIntS i x'
  | otherwise = Nothing

readEnumValueIntU :: T.Text -> T.Text -> Maybe EnumValue
readEnumValueIntU t x
  | Just (LowTypeIntU i) <- asLowTypeMaybe t
  , Just x' <- readMaybe $ T.unpack x = Just $ EnumValueIntU i x'
  | otherwise = Nothing

adjustPhase :: Meta -> WithEnv Meta
adjustPhase m = do
  i <- gets phase
  let newLoc = adjustPhase' i (metaLocation m)
  return $ m {metaLocation = newLoc, metaConstraintLocation = newLoc}

adjustPhase' :: Int -> Maybe Loc -> Maybe Loc
adjustPhase' _ Nothing = Nothing
adjustPhase' i (Just (_, l, c)) = Just (i, l, c)

-- newHole :: Meta -> WithEnv WeakTermPlus
-- newHole m = do
--   h <- newNameWith'' "hole-aux"
--   return (m, WeakTermZeta h)
asArrayKind :: TreePlus -> WithEnv ArrayKind
asArrayKind e@(_, TreeLeaf x) =
  case asArrayKindMaybe x of
    Nothing -> raiseSyntaxError (fst e) "SINT-TYPE | UINT-TYPE | FLOAT-TYPE"
    Just t -> return t
asArrayKind t = raiseSyntaxError (fst t) "LEAF"

toValueIntU :: IntSize -> Integer -> WeakTerm
toValueIntU size i = WeakTermEnumIntro $ EnumValueIntU size i

raiseSyntaxError :: Meta -> T.Text -> WithEnv a
raiseSyntaxError m form =
  raiseError m $ "couldn't match the input with the expected form: " <> form

-- the function `encodeChar` is adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
-- the license notice of this function is as follows:
--
--   Copyright (c) 2007, Galois Inc.
--   All rights reserved.
--
--   Redistribution and use in source and binary forms, with or without
--   modification, are permitted provided that the following conditions are met:
--       * Redistributions of source code must retain the above copyright
--         notice, this list of conditions and the following disclaimer.
--       * Redistributions in binary form must reproduce the above copyright
--         notice, this list of conditions and the following disclaimer in the
--         documentation and/or other materials provided with the distribution.
--       * Neither the name of Galois Inc. nor the
--         names of its contributors may be used to endorse or promote products
--         derived from this software without specific prior written permission.
--
--   THIS SOFTWARE IS PROVIDED BY Galois Inc. ``AS IS'' AND ANY
--   EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
--   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
--   DISCLAIMED. IN NO EVENT SHALL Galois Inc. BE LIABLE FOR ANY
--   DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
--   (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
--   LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
--   ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
--   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
--   SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
encodeChar :: Char -> [Word8]
encodeChar c = (map fromIntegral . go . ord) c
  where
    go oc
      | oc <= 0x7f = [oc]
      | oc <= 0x7ff = [0xc0 + (oc `shiftR` 6), 0x80 + oc .&. 0x3f]
      | oc <= 0xffff =
        [ 0xe0 + (oc `shiftR` 12)
        , 0x80 + ((oc `shiftR` 6) .&. 0x3f)
        , 0x80 + oc .&. 0x3f
        ]
      | otherwise =
        [ 0xf0 + (oc `shiftR` 18)
        , 0x80 + ((oc `shiftR` 12) .&. 0x3f)
        , 0x80 + ((oc `shiftR` 6) .&. 0x3f)
        , 0x80 + oc .&. 0x3f
        ]

-- the function `encode` is adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
-- the license notice of this function is as follows:
--
--   Copyright (c) 2007, Galois Inc.
--   All rights reserved.
--
--   Redistribution and use in source and binary forms, with or without
--   modification, are permitted provided that the following conditions are met:
--       * Redistributions of source code must retain the above copyright
--         notice, this list of conditions and the following disclaimer.
--       * Redistributions in binary form must reproduce the above copyright
--         notice, this list of conditions and the following disclaimer in the
--         documentation and/or other materials provided with the distribution.
--       * Neither the name of Galois Inc. nor the
--         names of its contributors may be used to endorse or promote products
--         derived from this software without specific prior written permission.
--
--   THIS SOFTWARE IS PROVIDED BY Galois Inc. ``AS IS'' AND ANY
--   EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
--   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
--   DISCLAIMED. IN NO EVENT SHALL Galois Inc. BE LIABLE FOR ANY
--   DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
--   (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
--   LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
--   ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
--   (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
--   SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
encode :: String -> [Word8]
encode input = concatMap encodeChar input
