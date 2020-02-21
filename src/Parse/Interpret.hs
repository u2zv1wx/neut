{-# LANGUAGE OverloadedStrings #-}

module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , interpretIter
  , interpretEnumItem
  , adjustPhase
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import Data.Char (chr, ord)
import Data.Maybe (fromMaybe)
import Data.Word (Word8)
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T
import qualified Text.Show.Pretty as Pr

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
    then throwError' $ "No such enum-type defined: " <> x
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
interpret (m, TreeNode [(_, TreeAtom "array"), dom, (_, TreeAtom kind)]) = do
  dom' <- interpret dom
  kind' <- asArrayKind kind
  m' <- adjustPhase m
  return (m', WeakTermArray dom' kind')
interpret (m, TreeNode ((_, TreeAtom "array-introduction"):(_, TreeAtom kind):es)) = do
  kind' <- asArrayKind kind
  es' <- mapM interpret es
  m' <- adjustPhase m
  return (m', WeakTermArrayIntro kind' es')
interpret (m, TreeNode [(_, TreeAtom "array-elimination"), (_, TreeAtom kind), (_, TreeNode xts), e1, e2]) = do
  kind' <- asArrayKind kind
  e1' <- interpret e1
  (xts', e2') <- interpretBinder xts e2
  m' <- adjustPhase m
  return (m', WeakTermArrayElim kind' xts' e1' e2')
interpret (m, TreeNode ((_, TreeAtom "struct"):ks)) = do
  ks' <- mapM asStructKind ks
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
  if null es
    then throwError' $ "interpret: syntax error:\n" <> T.pack (Pr.ppShow t)
    else interpret (m', TreeNode ((m, TreeAtom "pi-elimination") : es))

interpretIdentifierPlus :: TreePlus -> WithEnv IdentifierPlus
interpretIdentifierPlus (m, TreeAtom x) = do
  (m', x') <- interpretAtom (m, TreeAtom x)
  h <- newHole m'
  return (m', x', h)
interpretIdentifierPlus (_, TreeNode [x, t]) = do
  (m', x') <- interpretAtom x
  t' <- interpret t
  return (m', x', t')
interpretIdentifierPlus ut =
  throwError' $
  "interpretIdentifierPlus: syntax error:\n" <> T.pack (Pr.ppShow ut)

interpretIter :: TreePlus -> WithEnv Def
interpretIter (m, TreeNode [xt, (_, TreeNode xts), e]) = do
  xt' <- interpretIdentifierPlus xt
  (xts', e') <- interpretBinder xts e
  m' <- adjustPhase m
  return (m', xt', xts', e')
interpretIter _ = throwError' "interpretIter"

interpretAtom :: TreePlus -> WithEnv (Meta, Identifier)
interpretAtom (m, TreeAtom "_") = do
  m' <- adjustPhase m
  let m'' = m' {metaIsAppropriateAsCompletionCandidate = False}
  h <- newNameWith'' "H"
  return (m'', h)
interpretAtom (m, TreeAtom x) = do
  m' <- adjustPhase m
  return (m', asIdent x)
interpretAtom t =
  throwError' $ "interpretAtom: syntax error:\n" <> T.pack (Pr.ppShow t)

interpretEnumValueMaybe :: TreePlus -> WithEnv (Maybe EnumValue)
interpretEnumValueMaybe (_, TreeAtom x)
  | Just v <- readEnumValueNat x = return $ Just v
interpretEnumValueMaybe (_, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just v <- readEnumValueIntS t x = return $ Just v
interpretEnumValueMaybe (_, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just v <- readEnumValueIntU t x = return $ Just v
interpretEnumValueMaybe (_, TreeAtom x) = do
  b <- isDefinedEnum x
  if b
    then return $ Just $ EnumValueLabel x
    else return Nothing
interpretEnumValueMaybe _ = return Nothing

interpretEnumValue :: TreePlus -> WithEnv EnumValue
interpretEnumValue l = do
  ml' <- interpretEnumValueMaybe l
  case ml' of
    Just l' -> return l'
    Nothing ->
      throwError' $
      "interpretEnumValue: syntax error:\n" <> T.pack (Pr.ppShow l)

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
interpretClause e =
  throwError' $ "interpretClause: syntax error:\n " <> T.pack (Pr.ppShow e)

interpretStructIntro :: TreePlus -> WithEnv (WeakTermPlus, ArrayKind)
interpretStructIntro (_, TreeNode [e, k]) = do
  e' <- interpret e
  k' <- asStructKind k
  return (e', k')
interpretStructIntro e =
  throwError' $ "interpretStructIntro: syntax error:\n " <> T.pack (Pr.ppShow e)

interpretStructElim :: TreePlus -> WithEnv (Meta, Identifier, ArrayKind)
interpretStructElim (_, TreeNode [(m, TreeAtom x), k]) = do
  k' <- asStructKind k
  return (m, asIdent x, k')
interpretStructElim e =
  throwError' $ "interpretStructElim: syntax error:\n " <> T.pack (Pr.ppShow e)

interpretEnumItem :: [TreePlus] -> WithEnv [(T.Text, Int)]
interpretEnumItem ts = do
  xis <- interpretEnumItem' $ reverse ts
  if linearCheck (map snd xis)
    then return $ reverse xis
    else throwError'
           "found a collision of discriminant with previous definition"

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
interpretEnumItem'' t =
  throwError' $ "interpretEnumItem: syntax error:\n" <> T.pack (Pr.ppShow t)

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

asArrayKindMaybe :: LowType -> Maybe ArrayKind
asArrayKindMaybe (LowTypeIntS i) = Just $ ArrayKindIntS i
asArrayKindMaybe (LowTypeIntU i) = Just $ ArrayKindIntU i
asArrayKindMaybe (LowTypeFloat size) = Just $ ArrayKindFloat size
asArrayKindMaybe _ = Nothing

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

asArrayKind :: T.Text -> WithEnv ArrayKind
asArrayKind x =
  case asLowTypeMaybe x of
    Nothing -> throwError' "asArrayKind: syntax error"
    Just t -> do
      case asArrayKindMaybe t of
        Nothing -> throwError' "asArrayKind: syntax error"
        Just a -> return a

asStructKind :: TreePlus -> WithEnv ArrayKind
asStructKind (_, TreeAtom x) = asArrayKind x
asStructKind t =
  throwError' $ "asStructKind: syntax error:\n" <> T.pack (Pr.ppShow t)

-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
encodeChar :: Char -> [Word8]
encodeChar c = do
  let result = (map fromIntegral . go . ord) c
  assertP "encodeChar" result (decode result == [c])
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

-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
encode :: String -> [Word8]
encode input = do
  let result = concatMap encodeChar input
  assertP "encode" result (decode result == input)

-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
replacement_character :: Char
replacement_character = '\xfffd'

-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
-- this function is used only for assertion.
decode :: [Word8] -> String
decode [] = ""
decode (c:cs)
  | c < 0x80 = chr (fromEnum c) : decode cs
  | c < 0xc0 = replacement_character : decode cs
  | c < 0xe0 = multi1
  | c < 0xf0 = multi_byte 2 0xf 0x800
  | c < 0xf8 = multi_byte 3 0x7 0x10000
  | c < 0xfc = multi_byte 4 0x3 0x200000
  | c < 0xfe = multi_byte 5 0x1 0x4000000
  | otherwise = replacement_character : decode cs
  where
    multi1 =
      case cs of
        c1:ds
          | c1 .&. 0xc0 == 0x80 ->
            let d =
                  ((fromEnum c .&. 0x1f) `shiftL` 6) .|. fromEnum (c1 .&. 0x3f)
             in if d >= 0x000080
                  then toEnum d : decode ds
                  else replacement_character : decode ds
        _ -> replacement_character : decode cs
    multi_byte :: Int -> Word8 -> Int -> [Char]
    multi_byte i mask overlong = aux i cs (fromEnum (c .&. mask))
      where
        aux 0 rs acc
          | overlong <= acc &&
              acc <= 0x10ffff &&
              (acc < 0xd800 || 0xdfff < acc) && (acc < 0xfffe || 0xffff < acc) =
            chr acc : decode rs
          | otherwise = replacement_character : decode rs
        aux n (r:rs) acc
          | r .&. 0xc0 == 0x80 =
            aux (n - 1) rs $ shiftL acc 6 .|. fromEnum (r .&. 0x3f)
        aux _ rs _ = replacement_character : decode rs
