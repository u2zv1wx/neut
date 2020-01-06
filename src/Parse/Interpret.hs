module Parse.Interpret
  ( interpret
  , interpretIdentifierPlus
  , extractIdentifier
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.Bits ((.&.), shiftR)
import Data.Char (ord)
import Data.List (intercalate)
import Data.Word (Word8)
import Text.Read (readMaybe)
import qualified Text.Show.Pretty as Pr

import Data.Basic
import Data.Env
import Data.QuasiTerm
import Data.Tree

interpret :: TreePlus -> WithEnv QuasiTermPlus
--
-- foundational interpretations
--
interpret (m, TreeAtom "tau") = withMeta m QuasiTermTau
interpret (m, TreeNode [(_, TreeAtom "upsilon"), (_, TreeAtom x)]) =
  withMeta m $ QuasiTermUpsilon x
interpret (m, TreeNode [(_, TreeAtom "pi"), (_, TreeNode xts), t]) = do
  (xts', t') <- interpretBinder xts t
  withMeta m $ QuasiTermPi xts' t'
interpret (m, TreeNode [(_, TreeAtom "pi-introduction"), (_, TreeNode xts), e]) = do
  (xts', e') <- interpretBinder xts e
  withMeta m $ QuasiTermPiIntro xts' e'
interpret (m, TreeNode ((_, TreeAtom "pi-elimination"):e:es)) = do
  e' <- interpret e
  es' <- mapM interpret es
  withMeta m $ QuasiTermPiElim e' es'
interpret (m, TreeNode [(_, TreeAtom "mu"), xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  withMeta m $ QuasiTermMu xt' e'
interpret (m, TreeNode [(_, TreeAtom "zeta"), (_, TreeAtom x)]) = do
  x' <- interpretAtom x
  withMeta m $ QuasiTermZeta x'
interpret (m, TreeNode [(_, TreeAtom "constant"), (_, TreeAtom x)]) =
  withMeta m $ QuasiTermConst x
interpret (m, TreeNode [(_, TreeAtom "constant-declaration"), xt, e]) = do
  xt' <- interpretIdentifierPlus xt
  e' <- interpret e
  withMeta m $ QuasiTermConstDecl xt' e'
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntS i) <- asLowTypeMaybe t
  , Just x' <- readMaybe x = withMeta m $ QuasiTermIntS i x'
interpret (m, TreeNode [(_, TreeAtom t), (_, TreeAtom x)])
  | Just (LowTypeIntU i) <- asLowTypeMaybe t
  , Just x' <- readMaybe x = withMeta m $ QuasiTermIntU i x'
interpret (m, TreeNode [(_, TreeAtom "f16"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = do withMeta m $ QuasiTermFloat16 x'
interpret (m, TreeNode [(_, TreeAtom "f32"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = do withMeta m $ QuasiTermFloat32 x'
interpret (m, TreeNode [(_, TreeAtom "f64"), (_, TreeAtom x)])
  | Just x' <- readMaybe x = do withMeta m $ QuasiTermFloat64 x'
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)])
  | Just i <- readNatEnumType x =
    withMeta m $ QuasiTermEnum $ EnumTypeNatNum $ fromInteger i
interpret (m, TreeNode [(_, TreeAtom "enum"), (_, TreeAtom x)]) = do
  isEnum <- isDefinedEnumName x
  if not isEnum
    then throwError $ "No such enum-type defined: " ++ x
    else withMeta m $ QuasiTermEnum $ EnumTypeLabel x
interpret (m, TreeNode [(_, TreeAtom "enum-introduction"), l]) = do
  l' <- interpretEnumValue l
  withMeta m $ QuasiTermEnumIntro l'
interpret (m, TreeNode [(_, TreeAtom "enum-elimination"), e, (_, TreeNode cs)]) = do
  e' <- interpret e
  cs' <- mapM interpretClause cs
  withMeta m $ QuasiTermEnumElim e' cs'
interpret (m, TreeNode [(_, TreeAtom str), indexType])
  | Just kind <- withKindPrefix str "array" = do
    indexType' <- interpret indexType
    withMeta m $ QuasiTermArray kind indexType'
interpret (m, TreeNode ((_, TreeAtom str):cs))
  | Just kind <- withKindPrefix str "array-introduction" = do
    cs' <- mapM interpretClause cs
    let (ls, es) = unzip cs'
    ls' <- mapM asArrayIntro ls
    withMeta m $ QuasiTermArrayIntro kind (zip ls' es)
interpret (m, TreeNode [(_, TreeAtom str), e1, e2])
  | Just kind <- withKindPrefix str "array-elimination" = do
    e1' <- interpret e1
    e2' <- interpret e2
    withMeta m $ QuasiTermArrayElim kind e1' e2'
--
-- auxiliary interpretations
--
interpret (m, TreeAtom x)
  | Just x' <- readMaybe x = withMeta m $ QuasiTermInt x'
interpret (m, TreeAtom x)
  | Just x' <- readMaybe x = withMeta m $ QuasiTermFloat x'
interpret (m, TreeAtom x)
  | Just i <- readNatEnumType x =
    withMeta m $ QuasiTermEnum $ EnumTypeNatNum $ fromInteger i
interpret (m, TreeAtom x)
  | Just (i, j) <- readNatEnumValue x =
    withMeta m $ QuasiTermEnumIntro $ EnumValueNatNum i j
interpret (m, TreeAtom x)
  | Just str <- readMaybe x = do
    u8s <- forM (encode str) $ \u -> withMeta m (QuasiTermIntU 8 (toInteger u))
    let len = toInteger $ length u8s
    let ns = map (\i -> EnumValueNatNum len i) [0 .. (len - 1)]
    -- parse string as utf-8 encoded u8 array
    withMeta m $ QuasiTermArrayIntro (ArrayKindIntU 8) (zip ns u8s)
interpret (m, TreeAtom "_") = do
  h <- newNameWith "hole-aux"
  withMeta m $ QuasiTermZeta h
interpret t@(m, TreeAtom x) = do
  ml <- interpretEnumValueMaybe t
  case ml of
    Just l -> withMeta m $ QuasiTermEnumIntro l
    _ -> do
      isEnum <- isDefinedEnumName x
      if isEnum
        then withMeta m $ QuasiTermEnum $ EnumTypeLabel x
        else do
          cenv <- gets constantEnv
          if isConstant x || x `elem` cenv
            then withMeta m $ QuasiTermConst x
            else withMeta m $ QuasiTermUpsilon x
interpret t@(m, TreeNode es) =
  if null es
    then throwError $ "interpret: syntax error:\n" ++ Pr.ppShow t
    else interpret (m, TreeNode ((m, TreeAtom "pi-elimination") : es))

interpretIdentifierPlus :: TreePlus -> WithEnv IdentifierPlus
interpretIdentifierPlus (_, TreeAtom x) = do
  h <- newNameWith "hole-plus"
  return (x, (newWeakMetaTerminal, QuasiTermZeta h))
interpretIdentifierPlus (_, TreeNode [(_, TreeAtom x), t]) = do
  x' <- interpretAtom x
  t' <- interpret t
  return (x', t')
interpretIdentifierPlus ut =
  throwError $ "interpretIdentifierPlus: syntax error:\n" ++ Pr.ppShow ut

interpretAtom :: String -> WithEnv String
interpretAtom "_" = newNameWith "hole-explicit"
interpretAtom x = return x

interpretEnumValueMaybe :: TreePlus -> WithEnv (Maybe EnumValue)
interpretEnumValueMaybe (_, TreeAtom x)
  | Just (i, j) <- readNatEnumValue x = return $ Just $ EnumValueNatNum i j
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
    Nothing -> throwError $ "interpretEnumValue: syntax error:\n" ++ Pr.ppShow l

interpretBinder ::
     [TreePlus] -> TreePlus -> WithEnv ([IdentifierPlus], QuasiTermPlus)
interpretBinder xts t = do
  xts' <- mapM interpretIdentifierPlus xts
  t' <- interpret t
  return (xts', t')

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
interpretCase c = do
  l <- interpretEnumValue c
  return $ CaseValue l

interpretClause :: TreePlus -> WithEnv (Case, QuasiTermPlus)
interpretClause (_, TreeNode [c, e]) = do
  c' <- interpretCase c
  e' <- interpret e
  return (c', e')
interpretClause e =
  throwError $ "interpretClause: syntax error:\n " ++ Pr.ppShow e

asArrayIntro :: Case -> WithEnv EnumValue
asArrayIntro (CaseValue l) = return l
asArrayIntro CaseDefault = throwError "`default` cannot be used in array-intro"

withMeta :: TreeMeta -> QuasiTerm -> WithEnv QuasiTermPlus
withMeta m e = return (toWeakMetaNonTerminal m, e)

extractIdentifier :: TreePlus -> WithEnv Identifier
extractIdentifier (_, TreeAtom s) = return s
extractIdentifier t =
  throwError $ "interpretAtom: syntax error:\n" ++ Pr.ppShow t

withKindPrefix :: String -> String -> Maybe ArrayKind
withKindPrefix str base
  | (t:rest) <- wordsBy '-' str -- e.g. u8-array
  , base == intercalate "-" rest
  , Just t' <- asLowTypeMaybe t
  , Just kind <- asArrayKind t' = Just kind
withKindPrefix _ _ = Nothing

-- adopted from https://hackage.haskell.org/package/utf8-string-1.0.1.1/docs/src/Codec-Binary-UTF8-String.html
encodeChar :: Char -> [Word8]
encodeChar = map fromIntegral . go . ord
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
encode = concatMap encodeChar

toWeakMetaNonTerminal :: TreeMeta -> WeakMeta
toWeakMetaNonTerminal m = WeakMetaNonTerminal (treeMetaLocation m)

newWeakMetaTerminal :: WeakMeta
newWeakMetaTerminal = WeakMetaTerminal Nothing

isDefinedEnumName :: Identifier -> WithEnv Bool
isDefinedEnumName name = do
  env <- get
  let enumNameList = map fst $ enumEnv env
  return $ name `elem` enumNameList
