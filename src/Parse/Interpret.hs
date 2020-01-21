{-# LANGUAGE OverloadedStrings #-}

module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , extractIdentifier
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import Data.Char (chr, ord)
import Data.Word (Word8)
import Text.Read (readMaybe)

import qualified Data.HashMap.Strict as Map
import qualified Data.Text as T
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Env
import Data.Tree
import Data.WeakTerm

-- {} interpret {}
interpret :: TreePlus -> WithEnv WeakTermPlus
--
-- foundational interpretations
--
interpret (m, TreeAtom "tau") = return (m, WeakTermTau)
interpret (m, TreeNode [(_, TreeAtom "upsilon"), (_, TreeAtom x)]) =
  return (m, WeakTermUpsilon x)
interpret (m, TreeNode [(_, TreeAtom "pi"), (_, TreeNode xts), t]) = do
  (xts', t') <- interpretBinder xts t
  return (m, WeakTermPi xts' t')
interpret (m, TreeNode [(_, TreeAtom "pi-introduction"), (_, TreeNode xts), e]) = do
  (xts', e') <- interpretBinder xts e
  return (m, WeakTermPiIntro xts' e')
interpret (m, TreeNode ((_, TreeAtom "pi-elimination"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  return (m, WeakTermPiElim e' es')
interpret (m, TreeNode [(_, TreeAtom "iterate"), xt, (_, TreeNode xts), e]) = do
  xt' <- interpretIdentifierPlus xt
  (xts', e') <- interpretBinder xts e
  return (m, WeakTermIter xt' xts' e')
interpret (m, TreeNode [(_, TreeAtom "zeta"), (_, TreeAtom x)]) = do
  x' <- interpretAtom x
  return (m, WeakTermZeta x')
interpret (m, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom x)]) =
  return (m, WeakTermConst x)
interpret (m, TreeNode [(_, TreeAtom "constant-declaration"), xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  return (m, WeakTermConstDecl xt' e')
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntS i) <- asLowTypeMaybe t
  , Just x' <- readMaybe $ T.unpack x = return (m, WeakTermIntS i x')
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntU i) <- asLowTypeMaybe t
  , Just x' <- readMaybe $ T.unpack x = return (m, WeakTermIntU i x')
interpret (m, TreeNode [(_, TreeAtom "f16"), (_, TreeAtom x)])
  | Just x' <- readMaybe $ T.unpack x = return (m, WeakTermFloat16 x')
interpret (m, TreeNode [(_, TreeAtom "f32"), (_, TreeAtom x)])
  | Just x' <- readMaybe $ T.unpack x = return (m, WeakTermFloat32 x')
interpret (m, TreeNode [(_, TreeAtom "f64"), (_, TreeAtom x)])
  | Just x' <- readMaybe $ T.unpack x = return (m, WeakTermFloat64 x')
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)])
  | Just i <- readNatEnumType x =
    return (m, WeakTermEnum $ EnumTypeNatNum $ fromInteger i)
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)]) = do
  isEnum <- isDefinedEnumName x
  if not isEnum
    then throwError $ "No such enum-type defined: " <> x
    else return (m, WeakTermEnum $ EnumTypeLabel x)
interpret (m, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  l' <- interpretEnumValue l
  return (m, WeakTermEnumIntro l')
interpret (m, TreeNode ((_, TreeAtom "enum-elimination"):e:cs)) = do
  e' <- interpret e
  cs' <- mapM interpretClause cs
  h <- newHole m
  return (m, WeakTermEnumElim (e', h) cs')
interpret (m, TreeNode [(_, TreeAtom "array"), dom, (_, TreeAtom kind)]) = do
  dom' <- interpret dom
  kind' <- asArrayKind kind
  return (m, WeakTermArray dom' kind')
interpret (m, TreeNode ((_, TreeAtom "array-introduction"):(_, TreeAtom kind):es)) = do
  kind' <- asArrayKind kind
  es' <- mapM interpret es
  return (m, WeakTermArrayIntro kind' es')
interpret (m, TreeNode [(_, TreeAtom "array-elimination"), (_, TreeAtom kind), (_, TreeNode xts), e1, e2]) = do
  kind' <- asArrayKind kind
  e1' <- interpret e1
  (xts', e2') <- interpretBinder xts e2
  return (m, WeakTermArrayElim kind' xts' e1' e2')
interpret (m, TreeNode ((_, TreeAtom "struct"):ks)) = do
  ks' <- mapM asStructKind ks
  return (m, WeakTermStruct ks')
interpret (m, TreeNode ((_, TreeAtom "struct-introduction"):ets)) = do
  ets' <- mapM interpretStructIntro ets
  return (m, WeakTermStructIntro ets')
interpret (m, TreeNode [(_, TreeAtom "struct-elimination"), (_, TreeNode xts), e1, e2]) = do
  e1' <- interpret e1
  xts' <- mapM interpretStructElim xts
  e2' <- interpret e2
  return (m, WeakTermStructElim xts' e1' e2')
--
-- auxiliary interpretations
--
interpret (m, TreeAtom x)
  | Just x' <- readMaybe $ T.unpack x = do
    h <- newHole m
    return (m, WeakTermInt h x')
interpret (m, TreeAtom x)
  | Just x' <- readMaybe $ T.unpack x = do
    h <- newHole m
    return (m, WeakTermFloat h x')
interpret (m, TreeAtom x)
  | Just i <- readNatEnumType x =
    return (m, WeakTermEnum $ EnumTypeNatNum $ fromInteger i)
interpret (m, TreeAtom x)
  | Just (i, j) <- readNatEnumValue x =
    return (m, WeakTermEnumIntro $ EnumValueNatNum i j)
interpret (m, TreeAtom x)
  | Just str <- readMaybe $ T.unpack x = do
    u8s <- forM (encode str) $ \u -> return (m, WeakTermIntU 8 (toInteger u))
    -- parse string as utf-8 encoded u8 array
    return (m, WeakTermArrayIntro (ArrayKindIntU 8) u8s)
interpret t@(m, TreeAtom x) = do
  ml <- interpretEnumValueMaybe t
  isEnum <- isDefinedEnumName x
  case (ml, isEnum) of
    (Just l, _) -> return (m, WeakTermEnumIntro l)
    (_, True) -> return (m, WeakTermEnum $ EnumTypeLabel x)
    -- Note that constants are interpreted as variables at this stage.
    -- Those are reinterpreted into constants in Rename.
    -- This is to handle terms like `lam (i64 : bool). e` (i.e. bound variable
    -- with the same name of a constant) in saner way.
    (_, False) -> return (m, WeakTermUpsilon x)
interpret t@(m, TreeNode es) =
  if null es
    then throwError $ "interpret: syntax error:\n" <> T.pack (Pr.ppShow t)
    else interpret (m, TreeNode ((m, TreeAtom "pi-elimination") : es))

-- {} interpretIdentifierPlus {}
interpretIdentifierPlus :: TreePlus -> WithEnv IdentifierPlus
interpretIdentifierPlus (m, TreeAtom x) = do
  h <- newHole m
  return (x, h)
interpretIdentifierPlus (_, TreeNode [(_, TreeAtom x), t]) = do
  x' <- interpretAtom x
  t' <- interpret t
  return (x', t')
interpretIdentifierPlus ut =
  throwError $
  "interpretIdentifierPlus: syntax error:\n" <> T.pack (Pr.ppShow ut)

-- {} interpretAtom {}
interpretAtom :: Identifier -> WithEnv Identifier
interpretAtom "_" = newNameWith "hole-explicit"
interpretAtom x = return x

-- {} interpretEnumValueMaybe {}
interpretEnumValueMaybe :: TreePlus -> WithEnv (Maybe EnumValue)
interpretEnumValueMaybe (_, TreeAtom x)
  | Just (i, j) <- readNatEnumValue x = return $ Just $ EnumValueNatNum i j
interpretEnumValueMaybe (_, TreeAtom x) = do
  b <- isDefinedEnum x
  if b
    then return $ Just $ EnumValueLabel x
    else return Nothing
interpretEnumValueMaybe _ = return Nothing

-- {} interpretEnumValue {}
interpretEnumValue :: TreePlus -> WithEnv EnumValue
interpretEnumValue l = do
  ml' <- interpretEnumValueMaybe l
  case ml' of
    Just l' -> return l'
    Nothing ->
      throwError $ "interpretEnumValue: syntax error:\n" <> T.pack (Pr.ppShow l)

-- {} interpretBinder {}
-- `xts` はatomまたは(atom, tree)であることが想定されているけれど、どうせ、interpretIdentifierPlusは
-- 任意のtreeを読んで読めなかったらたんに失敗するだけだから問題なし。それゆえ事前条件がemptyになる。
interpretBinder ::
     [TreePlus] -> TreePlus -> WithEnv ([IdentifierPlus], WeakTermPlus)
interpretBinder xts t = do
  xts' <- mapM interpretIdentifierPlus xts
  t' <- interpret t
  return (xts', t')

-- {} interpretCase {}
interpretCase :: TreePlus -> WithEnv Case
--
-- foundational
--
interpretCase (_, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  CaseValue <$> interpretEnumValue l
interpretCase (_, TreeAtom "default") = return CaseDefault
--
-- auxiliary
--
interpretCase c = CaseValue <$> interpretEnumValue c

-- {} interpretClause {}
interpretClause :: TreePlus -> WithEnv (Case, WeakTermPlus)
interpretClause (_, TreeNode [c, e]) = do
  c' <- interpretCase c
  e' <- interpret e
  return (c', e')
interpretClause e =
  throwError $ "interpretClause: syntax error:\n " <> T.pack (Pr.ppShow e)

interpretStructIntro :: TreePlus -> WithEnv (WeakTermPlus, ArrayKind)
interpretStructIntro (_, TreeNode [e, k]) = do
  e' <- interpret e
  k' <- asStructKind k
  return (e', k')
interpretStructIntro e =
  throwError $ "interpretStructIntro: syntax error:\n " <> T.pack (Pr.ppShow e)

interpretStructElim :: TreePlus -> WithEnv (Identifier, ArrayKind)
interpretStructElim (_, TreeNode [(_, TreeAtom x), k]) = do
  k' <- asStructKind k
  return (x, k')
interpretStructElim e =
  throwError $ "interpretStructElim: syntax error:\n " <> T.pack (Pr.ppShow e)

-- {} extractIdentifier {}
extractIdentifier :: TreePlus -> WithEnv Identifier
extractIdentifier (_, TreeAtom s) = return s
extractIdentifier t =
  throwError $ "interpretAtom: syntax error:\n" <> T.pack (Pr.ppShow t)

-- {} isDefinedEnumName {}
isDefinedEnumName :: Identifier -> WithEnv Bool
isDefinedEnumName name = do
  env <- get
  -- let enumNameList = Map.elems $ enumEnv env
  let enumNameList = Map.keys $ enumEnv env
  return $ name `elem` enumNameList

newHole :: Meta -> WithEnv WeakTermPlus
newHole m = do
  h <- newNameWith "hole-aux"
  return (m, WeakTermZeta h)

asArrayKind :: Identifier -> WithEnv ArrayKind
asArrayKind x =
  case asLowTypeMaybe x of
    Nothing -> throwError "asArrayKind: syntax error"
    Just t -> do
      case asArrayKindMaybe t of
        Nothing -> throwError "asArrayKind: syntax error"
        Just a -> return a

asStructKind :: TreePlus -> WithEnv ArrayKind
asStructKind (_, TreeAtom x) = asArrayKind x
asStructKind t =
  throwError $ "asStructKind: syntax error:\n" <> T.pack (Pr.ppShow t)

-- {} encodechar {(the output is valid as utf8 string)}
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

-- {} encode {(the output is valid as utf-8 encoded string)}
-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
encode :: String -> [Word8]
encode input = do
  let result = concatMap encodeChar input
  assertP "encode" result (decode result == input)

-- {} replacement_character {}
-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
replacement_character :: Char
replacement_character = '\xfffd'

-- {} decode {}
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
