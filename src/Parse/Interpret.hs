module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , extractIdentifier
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits ((.&.), (.|.), shiftL, shiftR)
import Data.Char (chr, ord)
import Data.List (intercalate)
import Data.Word (Word8)
import Text.Read (readMaybe)
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Env
import Data.QuasiTerm
import Data.Tree

-- {} interpret {}
interpret :: TreePlus -> WithEnv QuasiTermPlus
--
-- foundational interpretations
--
interpret (m, TreeAtom "tau") = return (m, QuasiTermTau)
interpret (m, TreeNode [(_, TreeAtom "upsilon"), (_, TreeAtom x)]) =
  return (m, QuasiTermUpsilon x)
interpret (m, TreeNode [(_, TreeAtom "pi"), (_, TreeNode xts), t]) = do
  (xts', t') <- interpretBinder xts t
  return (m, QuasiTermPi xts' t')
interpret (m, TreeNode [(_, TreeAtom "pi-introduction"), (_, TreeNode xts), e]) = do
  (xts', e') <- interpretBinder xts e
  return (m, QuasiTermPiIntro xts' e')
interpret (m, TreeNode ((_, TreeAtom "pi-elimination"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  return (m, QuasiTermPiElim e' es')
interpret (m, TreeNode [(_, TreeAtom "mu"), xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  return (m, QuasiTermMu xt' e')
interpret (m, TreeNode [(_, TreeAtom "zeta"), (_, TreeAtom x)]) = do
  x' <- interpretAtom x
  return (m, QuasiTermZeta x')
interpret (m, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom x)]) =
  return (m, QuasiTermConst x)
interpret (m, TreeNode [(_, TreeAtom "constant-declaration"), xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  return (m, QuasiTermConstDecl xt' e')
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntS i) <- asLowTypeMaybe t
  , Just x' <- readMaybe x = return (m, QuasiTermIntS i x')
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntU i) <- asLowTypeMaybe t
  , Just x' <- readMaybe x = return (m, QuasiTermIntU i x')
interpret (m, TreeNode [(_, TreeAtom "f16"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = return (m, QuasiTermFloat16 x')
interpret (m, TreeNode [(_, TreeAtom "f32"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = return (m, QuasiTermFloat32 x')
interpret (m, TreeNode [(_, TreeAtom "f64"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = return (m, QuasiTermFloat64 x')
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)])
  | Just i <- readNatEnumType x =
    return (m, QuasiTermEnum $ EnumTypeNatNum $ fromInteger i)
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)]) = do
  isEnum <- isDefinedEnumName x
  if not isEnum
    then throwError $ "No such enum-type defined: " ++ x
    else return (m, QuasiTermEnum $ EnumTypeLabel x)
interpret (m, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  l' <- interpretEnumValue l
  return (m, QuasiTermEnumIntro l')
interpret (m, TreeNode ((_, TreeAtom "enum-elimination"):e:cs)) = do
  e' <- interpret e
  cs' <- mapM interpretClause cs
  return (m, QuasiTermEnumElim e' cs')
interpret (m, TreeNode [(_, TreeAtom str), indexType])
  | Just kind <- withKindPrefix str "array" = do
    indexType' <- interpret indexType
    return (m, QuasiTermArray kind indexType')
interpret (m, TreeNode ((_, TreeAtom str):cs))
  | Just kind <- withKindPrefix str "array-introduction" = do
    cs' <- mapM interpretClause cs
    let (ls, es) = unzip cs'
    ls' <- mapM asArrayIntro ls
    return (m, QuasiTermArrayIntro kind (zip ls' es))
interpret (m, TreeNode [(_, TreeAtom str), e1, e2])
  | Just kind <- withKindPrefix str "array-elimination" = do
    e1' <- interpret e1
    e2' <- interpret e2
    return (m, QuasiTermArrayElim kind e1' e2')
--
-- auxiliary interpretations
--
interpret (m, TreeAtom x)
  | Just x' <- readMaybe x = return (m, QuasiTermInt x')
interpret (m, TreeAtom x)
  | Just x' <- readMaybe x = return (m, QuasiTermFloat x')
interpret (m, TreeAtom x)
  | Just i <- readNatEnumType x =
    return (m, QuasiTermEnum $ EnumTypeNatNum $ fromInteger i)
interpret (m, TreeAtom x)
  | Just (i, j) <- readNatEnumValue x =
    return (m, QuasiTermEnumIntro $ EnumValueNatNum i j)
interpret (m, TreeAtom x)
  | Just str <- readMaybe x = do
    u8s <- forM (encode str) $ \u -> return (m, QuasiTermIntU 8 (toInteger u))
    let len = toInteger $ length u8s
    let ns = map (\i -> EnumValueNatNum len i) [0 .. (len - 1)]
    -- parse string as utf-8 encoded u8 array
    return (m, QuasiTermArrayIntro (ArrayKindIntU 8) (zip ns u8s))
interpret (m, TreeAtom "_") = do
  h <- newNameWith "hole-aux"
  return (m, QuasiTermZeta h)
interpret t@(m, TreeAtom x) = do
  ml <- interpretEnumValueMaybe t
  case ml of
    Just l -> return (m, QuasiTermEnumIntro l)
    _ -> do
      isEnum <- isDefinedEnumName x
      if isEnum
        then return (m, QuasiTermEnum $ EnumTypeLabel x)
        else do
          cenv <- gets constantEnv
          if isConstant x || x `elem` cenv
            then return (m, QuasiTermConst x)
            else return (m, QuasiTermUpsilon x)
interpret t@(m, TreeNode es) =
  if null es
    then throwError $ "interpret: syntax error:\n" ++ Pr.ppShow t
    else interpret (m, TreeNode ((m, TreeAtom "pi-elimination") : es))

-- {} interpretIdentifierPlus {}
interpretIdentifierPlus :: TreePlus -> WithEnv IdentifierPlus
interpretIdentifierPlus (_, TreeAtom x) = do
  h <- newNameWith "hole-plus"
  return (x, (emptyMeta, QuasiTermZeta h))
interpretIdentifierPlus (_, TreeNode [(_, TreeAtom x), t]) = do
  x' <- interpretAtom x
  t' <- interpret t
  return (x', t')
interpretIdentifierPlus ut =
  throwError $ "interpretIdentifierPlus: syntax error:\n" ++ Pr.ppShow ut

-- {} interpretAtom {}
interpretAtom :: String -> WithEnv String
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
    Nothing -> throwError $ "interpretEnumValue: syntax error:\n" ++ Pr.ppShow l

-- {} interpretBinder {}
-- `xts` はatomまたは(atom, tree)であることが想定されているけれど、どうせ、interpretIdentifierPlusは
-- 任意のtreeを読んで読めなかったらたんに失敗するだけだから問題なし。それゆえ事前条件がemptyになる。
interpretBinder ::
     [TreePlus] -> TreePlus -> WithEnv ([IdentifierPlus], QuasiTermPlus)
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
interpretClause :: TreePlus -> WithEnv (Case, QuasiTermPlus)
interpretClause (_, TreeNode [c, e]) = do
  c' <- interpretCase c
  e' <- interpret e
  return (c', e')
interpretClause e =
  throwError $ "interpretClause: syntax error:\n " ++ Pr.ppShow e

-- {} asArrayIntro {}
asArrayIntro :: Case -> WithEnv EnumValue
asArrayIntro (CaseValue l) = return l
asArrayIntro CaseDefault = throwError "`default` cannot be used in array-intro"

-- {} extractIdentifier {}
extractIdentifier :: TreePlus -> WithEnv Identifier
extractIdentifier (_, TreeAtom s) = return s
extractIdentifier t =
  throwError $ "interpretAtom: syntax error:\n" ++ Pr.ppShow t

-- {} withKindPrefix {}
-- 「-」でsplitして、第1要素がarraykindとして妥当で、かつ第2要素以降をconcatしたものがbaseと一致していたら、
-- arraykindを返す。たとえば"u8-array"と"array"が入力ならu8を、"f64-array-introduction"と"array-introduction"が
-- 入力ならf64を返す。
withKindPrefix ::
     String -- "u8-array", "u16-hoo", "f64-hogehoge"
  -> String -- "array", "hoo", "hogehoge"
  -> Maybe ArrayKind
withKindPrefix str base
  | (t:rest) <- wordsBy '-' str -- e.g. u8-array
  , base == intercalate "-" rest
  , Just t' <- asLowTypeMaybe t
  , Just kind <- asArrayKind t' = Just kind
withKindPrefix _ _ = Nothing

-- {} isDefinedEnumName {}
isDefinedEnumName :: Identifier -> WithEnv Bool
isDefinedEnumName name = do
  env <- get
  let enumNameList = map fst $ enumEnv env
  return $ name `elem` enumNameList

-- {} encodeChar {(the output is valid as utf8 string)}
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
