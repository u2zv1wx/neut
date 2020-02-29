{-# LANGUAGE OverloadedStrings #-}

module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , interpretIter
  , interpretEnumItem
  , adjustPhase
  , readEnumValueIntU
  , raiseSyntaxError
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits ((.&.), shiftR)
import Data.Char (ord)
import Data.Maybe (fromMaybe)
import Data.Word (Word8)
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T

-- import qualified Text.Show.Pretty as Pr
import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm

interpret :: TreePlus -> WithEnv WeakTermPlus
--
-- foundational interpretations
--
interpret (m, TreeAtom "tau") = do
  m' <- adjustPhase m
  l <- newCount
  return (m', WeakTermTau l)
interpret (m, TreeNode [(_, TreeAtom "upsilon"), (_, TreeAtom x)]) = do
  m' <- adjustPhase m
  return (m', WeakTermUpsilon $ asIdent x)
interpret (m, TreeNode [(_, TreeAtom "pi"), (_, TreeNode xts), t]) = do
  (xts', t') <- interpretBinder xts t
  mls <- piUnivLevelsfrom xts' t'
  m' <- adjustPhase m
  return (m', WeakTermPi mls xts' t')
interpret (m, TreeNode [(_, TreeAtom "pi-introduction"), (_, TreeNode xts), e]) = do
  (xts', e') <- interpretBinder xts e
  m' <- adjustPhase m
  return (m', WeakTermPiIntro xts' e')
interpret (m, TreeNode ((_, TreeAtom "pi-elimination"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  m' <- adjustPhase m
  return (m', WeakTermPiElim e' es')
interpret (m, TreeNode [(_, TreeAtom "sigma"), (_, TreeNode xts), t]) = do
  xts' <- mapM interpretIdentifierPlus xts
  t' <- interpret t
  placeholder <- newNameWith' "cod"
  m' <- adjustPhase m
  return (m', WeakTermSigma $ xts' ++ [(fst t', placeholder, t')])
interpret (m, TreeNode ((_, TreeAtom "sigma-introduction"):es)) = do
  m' <- adjustPhase m
  h <- newHole m'
  es' <- mapM interpret es
  return (m', WeakTermSigmaIntro h es')
interpret (m, TreeNode [(_, TreeAtom "sigma-elimination"), (_, TreeNode xts), e1, e2]) = do
  xts' <- mapM interpretIdentifierPlus xts
  e1' <- interpret e1
  e2' <- interpret e2
  m' <- adjustPhase m
  h <- newHole m'
  return (m', WeakTermSigmaElim h xts' e1' e2')
interpret (m, TreeNode [(_, TreeAtom "iterate"), xt, xts@(_, TreeNode _), e]) = do
  (m', xt', xts', e') <- interpretIter (m, TreeNode [xt, xts, e])
  return (m', WeakTermIter xt' xts' e')
interpret (m, TreeNode [(_, TreeAtom "zeta"), x]) = do
  (_, x') <- interpretAtom x
  m' <- adjustPhase m
  let m'' = m' {metaIsAppropriateAsCompletionCandidate = False}
  return (m'', WeakTermZeta x')
interpret (m, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom x)]) = do
  m' <- adjustPhase m
  return (m', WeakTermConst $ asIdent x)
interpret (m, TreeNode [(_, TreeAtom "f16"), (_, TreeAtom x)])
  | Just x' <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    return (m', WeakTermFloat16 x')
interpret (m, TreeNode [(_, TreeAtom "f32"), (_, TreeAtom x)])
  | Just x' <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    return (m', WeakTermFloat32 x')
interpret (m, TreeNode [(_, TreeAtom "f64"), (_, TreeAtom x)])
  | Just x' <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    return (m', WeakTermFloat64 x')
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)])
  | Just i <- readEnumTypeIntS x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeIntS i)
  | Just i <- readEnumTypeIntU x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeIntU i)
  | Just i <- readEnumTypeNat x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeNat i)
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)]) = do
  isEnum <- isDefinedEnumName x
  m' <- adjustPhase m
  if not isEnum
    then raiseError m $ "no such enum-type is defined: " <> x
    else return (m', WeakTermEnum $ EnumTypeLabel x)
interpret (m, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  l' <- interpretEnumValue l
  m' <- adjustPhase m
  return (m', WeakTermEnumIntro l')
interpret (m, TreeNode ((_, TreeAtom "enum-elimination"):e:cs)) = do
  e' <- interpret e
  cs' <- mapM interpretClause cs
  m' <- adjustPhase m
  h <- newHole m'
  return (m', WeakTermEnumElim (e', h) cs')
interpret (m, TreeNode [(_, TreeAtom "array"), dom, kind]) = do
  dom' <- interpret dom
  kind' <- asArrayKind kind
  m' <- adjustPhase m
  return (m', WeakTermArray dom' kind')
interpret (m, TreeNode ((_, TreeAtom "array-introduction"):kind:es)) = do
  kind' <- asArrayKind kind
  es' <- mapM interpret es
  m' <- adjustPhase m
  return (m', WeakTermArrayIntro kind' es')
interpret (m, TreeNode [(_, TreeAtom "array-elimination"), kind, (_, TreeNode xts), e1, e2]) = do
  kind' <- asArrayKind kind
  e1' <- interpret e1
  (xts', e2') <- interpretBinder xts e2
  m' <- adjustPhase m
  return (m', WeakTermArrayElim kind' xts' e1' e2')
interpret (m, TreeNode ((_, TreeAtom "struct"):ks)) = do
  ks' <- mapM asArrayKind ks
  m' <- adjustPhase m
  return (m', WeakTermStruct ks')
interpret (m, TreeNode ((_, TreeAtom "struct-introduction"):ets)) = do
  ets' <- mapM interpretStructIntro ets
  m' <- adjustPhase m
  return (m', WeakTermStructIntro ets')
interpret (m, TreeNode [(_, TreeAtom "struct-elimination"), (_, TreeNode xts), e1, e2]) = do
  e1' <- interpret e1
  xts' <- mapM interpretStructElim xts
  e2' <- interpret e2
  m' <- adjustPhase m
  return (m', WeakTermStructElim xts' e1' e2')
--
-- auxiliary interpretations
--
interpret (m, TreeNode ((_, TreeAtom "product"):ts)) = do
  ts' <- mapM interpret ts
  let ms = map fst ts'
  xs <- mapM (const $ newNameWith' "sig") ts'
  m' <- adjustPhase m
  return (m', WeakTermSigma (zip3 ms xs ts'))
interpret (m, TreeAtom x)
  | Just x' <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    h <- newHole m'
    return (m', WeakTermInt h x')
interpret (m, TreeAtom x)
  | Just x' <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    h <- newHole m'
    return (m', WeakTermFloat h x')
interpret (m, TreeAtom x)
  | Just i <- readEnumTypeIntS x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeIntS i)
  | Just i <- readEnumTypeIntU x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeIntU i)
  | Just i <- readEnumTypeNat x = do
    m' <- adjustPhase m
    return (m', WeakTermEnum $ EnumTypeNat i)
interpret (m, TreeAtom x)
  | Just v <- readEnumValueNat x = do
    m' <- adjustPhase m
    return (m', WeakTermEnumIntro v)
interpret (m, TreeAtom x)
  | Just str <- readMaybe $ T.unpack x = do
    m' <- adjustPhase m
    u8s <- forM (encode str) $ \u -> return (m', toValueIntU 8 (toInteger u))
    -- parse string as utf-8 encoded u8 array
    return (m', WeakTermArrayIntro (ArrayKindIntU 8) u8s)
interpret t@(m, TreeAtom x) = do
  ml <- interpretEnumValueMaybe t
  isEnum <- isDefinedEnumName x
  m' <- adjustPhase m
  case (ml, isEnum) of
    (Just l, _) -> return (m', WeakTermEnumIntro l)
    (_, True) -> return (m', WeakTermEnum $ EnumTypeLabel x)
    -- Note that constants are interpreted as variables at this stage.
    -- Those are reinterpreted into constants in Rename.
    -- This is to handle terms like `lam (i64 : bool). e` (i.e. bound variable
    -- with the same name of a constant) in saner way.
    (_, False) -> return (m', WeakTermUpsilon $ asIdent x)
interpret t@(m, TreeNode es) = do
  m' <- adjustPhase m
  ml <- interpretEnumValueMaybe t
  case ml of
    Just l -> return (m', WeakTermEnumIntro l)
    _ -> do
      if null es
        then raiseSyntaxError t "(TREE ...)"
        else interpret (m', TreeNode ((m, TreeAtom "pi-elimination") : es))

--  m' <- adjustPhase m
interpretIdentifierPlus :: TreePlus -> WithEnv IdentifierPlus
interpretIdentifierPlus (m, TreeAtom x) = do
  (m', x') <- interpretAtom (m, TreeAtom x)
  h <- newHole m'
  return (m', x', h)
interpretIdentifierPlus (_, TreeNode [x, t]) = do
  (m', x') <- interpretAtom x
  t' <- interpret t
  return (m', x', t')
interpretIdentifierPlus t = raiseSyntaxError t "(LEAF TREE)"

interpretIter :: TreePlus -> WithEnv Def
interpretIter (m, TreeNode [xt, (_, TreeNode xts), e]) = do
  xt' <- interpretIdentifierPlus xt
  (xts', e') <- interpretBinder xts e
  m' <- adjustPhase m
  return (m', xt', xts', e')
interpretIter t = raiseSyntaxError t "(TREE TREE TREE)"

interpretAtom :: TreePlus -> WithEnv (Meta, Identifier)
interpretAtom (m, TreeAtom "_") = do
  m' <- adjustPhase m
  let m'' = m' {metaIsAppropriateAsCompletionCandidate = False}
  h <- newNameWith'' "H"
  return (m'', h)
interpretAtom (m, TreeAtom x) = do
  m' <- adjustPhase m
  return (m', asIdent x)
interpretAtom t = raiseSyntaxError t "LEAF"

interpretEnumValueMaybe :: TreePlus -> WithEnv (Maybe EnumValue)
interpretEnumValueMaybe t =
  (Just <$> interpretEnumValue t) `catchError` (const $ return Nothing)

interpretEnumValue :: TreePlus -> WithEnv EnumValue
interpretEnumValue (m, TreeAtom x) = do
  b <- isDefinedEnum x
  case (readEnumValueNat x, b) of
    (Just v, _) -> return v
    (_, True) -> return $ EnumValueLabel x
    _ -> raiseError m $ "no such enum-value is defined: " <> x
interpretEnumValue e@(m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)]) = do
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
    _ -> raiseSyntaxError e "(SINT-TYPE INT) | (UINT-TYPE INT)"
interpretEnumValue t = raiseSyntaxError t "LEAF | (LEAF LEAF)"

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
interpretWeakCase (_, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  weakenEnumValue <$> interpretEnumValue l
interpretWeakCase (_, TreeAtom "default") = return WeakCaseDefault
--
-- auxiliary
--
interpretWeakCase c
  | (m, TreeAtom i) <- c
  , Just i' <- readMaybe $ T.unpack i = do
    h <- newHole m
    return $ WeakCaseInt h i'
  | otherwise = weakenEnumValue <$> interpretEnumValue c

interpretClause :: TreePlus -> WithEnv (WeakCase, WeakTermPlus)
interpretClause (_, TreeNode [c, e]) = do
  c' <- interpretWeakCase c
  e' <- interpret e
  return (c', e')
interpretClause e = raiseSyntaxError e "(TREE TREE)"

interpretStructIntro :: TreePlus -> WithEnv (WeakTermPlus, ArrayKind)
interpretStructIntro (_, TreeNode [e, k]) = do
  e' <- interpret e
  k' <- asArrayKind k
  return (e', k')
interpretStructIntro e = raiseSyntaxError e "(TREE TREE)"

interpretStructElim :: TreePlus -> WithEnv (Meta, Identifier, ArrayKind)
interpretStructElim (_, TreeNode [(m, TreeAtom x), k]) = do
  k' <- asArrayKind k
  return (m, asIdent x, k')
interpretStructElim e = raiseSyntaxError e "(LEAF TREE)"

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
interpretEnumItem'' (_, TreeAtom s) = return (s, Nothing)
interpretEnumItem'' (_, TreeNode [(_, TreeAtom s), (_, TreeAtom i)])
  | Just i' <- readMaybe $ T.unpack i = return (s, Just i')
interpretEnumItem'' t = raiseSyntaxError t "LEAF | (LEAF LEAF)"

headDiscriminantOf :: [(T.Text, Int)] -> Int
headDiscriminantOf [] = 0
headDiscriminantOf ((_, i):_) = i

isDefinedEnum :: T.Text -> WithEnv Bool
isDefinedEnum name = do
  env <- get
  let labelList = join $ Map.elems $ enumEnv env
  return $ name `elem` map fst labelList

isDefinedEnumName :: T.Text -> WithEnv Bool
isDefinedEnumName name = do
  env <- get
  let enumNameList = Map.keys $ enumEnv env
  return $ name `elem` enumNameList

readEnumType :: Char -> T.Text -> Int -> (Maybe Int)
readEnumType c str k -- n1, n2, ..., n{i}, ..., n{2^64}
  | T.length str >= 2
  , T.head str == c
  , Just i <- (readMaybe $ T.unpack $ T.tail str :: Maybe Int)
  , 1 <= toInteger i && toInteger i <= 2 ^ k = Just i
readEnumType _ _ _ = Nothing

readEnumTypeNat :: T.Text -> (Maybe Int)
readEnumTypeNat str = readEnumType 'n' str 64

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

readEnumValueNat :: T.Text -> Maybe EnumValue
readEnumValueNat str -- n1-0, n2-0, n2-1, ...
  | T.length str >= 4
  , T.head str == 'n'
  , [iStr, jStr] <- wordsBy '-' (T.tail str)
  , Just i <- readMaybe $ T.unpack iStr
  , 1 <= toInteger i && toInteger i <= 2 ^ (64 :: Integer)
  , Just j <- readMaybe $ T.unpack jStr
  , 0 <= toInteger j && toInteger j <= toInteger i - 1 = Just $ EnumValueNat i j
  | otherwise = Nothing

adjustPhase :: Meta -> WithEnv Meta
adjustPhase m = do
  i <- gets phase
  let newLoc = adjustPhase' i (metaLocation m)
  return $ m {metaLocation = newLoc, metaConstraintLocation = newLoc}

adjustPhase' :: Int -> Maybe Loc -> Maybe Loc
adjustPhase' _ Nothing = Nothing
adjustPhase' i (Just (_, l, c)) = Just (i, l, c)

newHole :: Meta -> WithEnv WeakTermPlus
newHole m = do
  h <- newNameWith'' "hole-aux"
  return (m, WeakTermZeta h)

-- asArrayKind :: T.Text -> WithEnv ArrayKind
asArrayKind :: TreePlus -> WithEnv ArrayKind
asArrayKind e@(_, TreeAtom x) =
  case asArrayKindMaybe x of
    Nothing -> raiseSyntaxError e "SINT-TYPE | UINT-TYPE | FLOAT-TYPE"
    Just t -> return t
asArrayKind t = raiseSyntaxError t "LEAF"

toValueIntU :: IntSize -> Integer -> WeakTerm
toValueIntU size i = WeakTermEnumIntro $ EnumValueIntU size i

raiseSyntaxError :: TreePlus -> T.Text -> WithEnv a
raiseSyntaxError e form =
  raiseError (fst e) $
  "couldn't interpret the input with the expected form:\n- " <>
  showAsSExp e <> "\n- " <> form

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
  -- let result = (map fromIntegral . go . ord) c
  -- assertP "encodeChar" result (decode result == [c])
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
  -- let result = concatMap encodeChar input
  -- assertP "encode" result (decode result == input)
-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
-- replacement_character :: Char
-- replacement_character = '\xfffd'
-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
-- this function is used only for assertion.
-- decode :: [Word8] -> String
-- decode [] = ""
-- decode (c:cs)
--   | c < 0x80 = chr (fromEnum c) : decode cs
--   | c < 0xc0 = replacement_character : decode cs
--   | c < 0xe0 = multi1
--   | c < 0xf0 = multi_byte 2 0xf 0x800
--   | c < 0xf8 = multi_byte 3 0x7 0x10000
--   | c < 0xfc = multi_byte 4 0x3 0x200000
--   | c < 0xfe = multi_byte 5 0x1 0x4000000
--   | otherwise = replacement_character : decode cs
--   where
--     multi1 =
--       case cs of
--         c1:ds
--           | c1 .&. 0xc0 == 0x80 ->
--             let d =
--                   ((fromEnum c .&. 0x1f) `shiftL` 6) .|. fromEnum (c1 .&. 0x3f)
--              in if d >= 0x000080
--                   then toEnum d : decode ds
--                   else replacement_character : decode ds
--         _ -> replacement_character : decode cs
--     multi_byte :: Int -> Word8 -> Int -> [Char]
--     multi_byte i mask overlong = aux i cs (fromEnum (c .&. mask))
--       where
--         aux 0 rs acc
--           | overlong <= acc &&
--               acc <= 0x10ffff &&
--               (acc < 0xd800 || 0xdfff < acc) && (acc < 0xfffe || 0xffff < acc) =
--             chr acc : decode rs
--           | otherwise = replacement_character : decode rs
--         aux n (r:rs) acc
--           | r .&. 0xc0 == 0x80 =
--             aux (n - 1) rs $ shiftL acc 6 .|. fromEnum (r .&. 0x3f)
--         aux _ rs _ = replacement_character : decode rs
