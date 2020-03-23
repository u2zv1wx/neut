{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.Basic where

import Data.Hashable
import GHC.Generics (Generic)
import Path

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Maybe (fromMaybe)
import Text.Read

newtype Identifier =
  I (T.Text, Int)
  deriving (Generic, Eq, Ord)

instance Hashable Identifier

asText :: Identifier -> T.Text
asText (I (s, _)) = s

asText' :: Identifier -> T.Text
asText' (I (s, i)) = s <> "-" <> T.pack (show i)

asText'' :: Identifier -> T.Text
asText'' (I (_, i)) = "_" <> T.pack (show i)

asIdent :: T.Text -> Identifier
asIdent s = I (s, 0)

asInt :: Identifier -> Int
asInt (I (_, i)) = i

instance Show Identifier where
  show (I (s, i)) = T.unpack s ++ "-" ++ show i

-- note that UnivLevel is just a name of the level of a universe (i.e. the integer
-- itself is not the level of the universe)
type UnivLevel = Int

newtype UnivLevelPlus =
  UnivLevelPlus (Meta, UnivLevel)

instance Show UnivLevelPlus where
  show (UnivLevelPlus (_, l)) = "[" ++ show l ++ "]"

instance Eq UnivLevelPlus where
  (UnivLevelPlus (_, l1)) == (UnivLevelPlus (_, l2)) = l1 == l2

type UnivParams = IntMap.IntMap UnivLevel

type Phase = Int

type Line = Int

type Column = Int

type Loc = (Phase, Line, Column)

data Meta =
  Meta
    { metaFileName :: Maybe (Path Abs File)
    , metaLocation :: Maybe Loc
    , metaConstraintLocation :: Maybe Loc
    , metaIsPublic :: Bool
    , metaIsAppropriateAsCompletionCandidate :: Bool
    , metaUnivParams :: UnivParams
    , metaIsExplicit :: Bool
    }

-- required to derive the eqality on WeakTerm
instance Eq Meta where
  _ == _ = True

instance Show Meta where
  show _ = "_"

instance Ord Meta where
  compare _ _ = EQ

showMeta :: Meta -> String
showMeta m =
  case (metaFileName m, metaConstraintLocation m) of
    (Just name, Nothing) -> toFilePath name
    (Just name, Just (_, l, c)) ->
      toFilePath name ++ ":" ++ show l ++ ":" ++ show c
    (Nothing, Nothing) -> "_"
    (Nothing, Just (_, l, c)) -> "<unknown-file>:" ++ show l ++ ":" ++ show c

showMeta' :: Meta -> String
showMeta' m =
  case (metaFileName m, metaConstraintLocation m) of
    (Just name, Nothing) -> toFilePath name
    (Just name, Just (ph, l, c)) ->
      toFilePath name ++ ":" ++ show ph ++ ":" ++ show l ++ ":" ++ show c
    (Nothing, Nothing) -> "_"
    (Nothing, Just (ph, l, c)) ->
      "<unknown-file>:" ++ show ph ++ ":" ++ show l ++ ":" ++ show c

supMeta :: Meta -> Meta -> Meta
supMeta m1 m2
  | metaConstraintLocation m1 < metaConstraintLocation m2 =
    m1 {metaConstraintLocation = metaConstraintLocation m2}
  | otherwise = m1

newMeta :: Int -> Int -> Path Abs File -> Meta
newMeta l c path = do
  Meta
    { metaFileName = Just path
    , metaLocation = Just (0, l, c)
    , metaConstraintLocation = Just (0, l, c)
    , metaIsPublic = True
    , metaIsAppropriateAsCompletionCandidate = True
    , metaUnivParams = IntMap.empty
    , metaIsExplicit = False
    }

type PosInfo = (Path Abs File, Loc)

getPosInfo :: Meta -> Maybe PosInfo
getPosInfo m =
  case (metaFileName m, metaLocation m) of
    (Just name, Just loc) -> return (name, loc)
    _ -> Nothing

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) = toFilePath path ++ ":" ++ show l ++ ":" ++ show c

type IntSize = Int

data FloatSize
  = FloatSize16
  | FloatSize32
  | FloatSize64
  deriving (Eq, Show)

asFloatSize :: Int -> Maybe FloatSize
asFloatSize 16 = Just FloatSize16
asFloatSize 32 = Just FloatSize32
asFloatSize 64 = Just FloatSize64
asFloatSize _ = Nothing

data EnumType
  = EnumTypeLabel T.Text
  | EnumTypeIntS Int -- i{k}
  | EnumTypeIntU Int -- u{k}
  deriving (Show, Eq)

data EnumValue
  = EnumValueIntS IntSize Integer
  | EnumValueIntU IntSize Integer
  | EnumValueLabel T.Text
  deriving (Show, Eq, Ord)

data Case
  = CaseValue EnumValue
  | CaseDefault
  deriving (Show, Eq, Ord)

data LowType
  = LowTypeIntS IntSize
  | LowTypeIntU IntSize
  | LowTypeFloat FloatSize
  | LowTypeVoid -- to represent the cod of free
  | LowTypeVoidPtr
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStructPtr [LowType]
  | LowTypeArrayPtr Int LowType -- [n x LOWTYPE]*
  | LowTypeIntS64Ptr
  deriving (Eq, Show)

asLowType :: Identifier -> LowType
asLowType (I (n, _)) = fromMaybe (LowTypeIntS 64) (asLowTypeMaybe n)

-- これasArrayKindMaybeから実装したほうがよさそう？
asLowTypeMaybe :: T.Text -> Maybe LowType
asLowTypeMaybe s =
  case T.uncons s of
    Just ('i', rest)
      | Just n <- readMaybe $ T.unpack rest
      , 0 < n && n <= 64 -> Just $ LowTypeIntS n
    Just ('u', rest)
      | Just n <- readMaybe $ T.unpack rest
      , 0 < n && n <= 64 -> Just $ LowTypeIntU n
    Just ('f', rest)
      | Just n <- readMaybe $ T.unpack rest
      , Just size <- asFloatSize n -> Just $ LowTypeFloat size
    _ -> Nothing

asIntS :: Integral a => a -> a -> a
asIntS size n = do
  let upperBound = 2 ^ (size - 1)
  let m = 2 * upperBound
  let a = mod n m
  if a >= upperBound
    then a - m
    else a

asIntU :: Integral a => a -> a -> a
asIntU size n = mod n (2 ^ size)

sizeAsInt :: FloatSize -> Int
sizeAsInt FloatSize16 = 16
sizeAsInt FloatSize32 = 32
sizeAsInt FloatSize64 = 64

data ArrayKind
  = ArrayKindIntS Int
  | ArrayKindIntU Int
  | ArrayKindFloat FloatSize
  | ArrayKindVoidPtr
  deriving (Show, Eq)

voidPtr :: LowType
voidPtr = LowTypeVoidPtr

arrVoidPtr :: ArrayKind
arrVoidPtr = ArrayKindVoidPtr

asArrayAccessMaybe :: T.Text -> Maybe LowType
asArrayAccessMaybe name
  | [typeStr, "array-access"] <- wordsBy ':' name = asLowTypeMaybe typeStr
  | otherwise = Nothing

-- asArrayAccessMaybe :: Identifier -> Maybe LowType
-- asArrayAccessMaybe (I (name, _))
--   | ["array-access", typeStr] <- sepAtLast '-' name
--   , Just lowType <- asLowTypeMaybe typeStr = Just lowType
-- asArrayAccessMaybe _ = Nothing
-- sepAtLast :: Char -> T.Text -> [T.Text]
-- sepAtLast c s =
--   case wordsBy c s of
--     [] -> []
--     [s'] -> [s']
--     ss -> [T.intercalate (T.singleton c) (init ss), last ss]
lowTypeToArrayKindMaybe :: LowType -> Maybe ArrayKind
lowTypeToArrayKindMaybe (LowTypeIntS i) = Just $ ArrayKindIntS i
lowTypeToArrayKindMaybe (LowTypeIntU i) = Just $ ArrayKindIntU i
lowTypeToArrayKindMaybe (LowTypeFloat size) = Just $ ArrayKindFloat size
lowTypeToArrayKindMaybe _ = Nothing

asArrayKindMaybe :: T.Text -> Maybe ArrayKind
asArrayKindMaybe "" = Nothing
asArrayKindMaybe s
  | 'i' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n <= 64 = Just $ ArrayKindIntS n
asArrayKindMaybe s
  | 'u' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n <= 64 = Just $ ArrayKindIntU n
asArrayKindMaybe s
  | 'f' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , Just size <- asFloatSize n = Just $ ArrayKindFloat size
asArrayKindMaybe _ = Nothing

data UnaryOp
  = UnaryOpNeg LowType -- fneg : X -> X
  | UnaryOpTrunc LowType LowType -- trunc, fptrunc : X -> Y
  | UnaryOpZext LowType LowType -- zext
  | UnaryOpSext LowType LowType -- sext
  | UnaryOpFpExt LowType LowType -- fpext
  | UnaryOpTo LowType LowType -- fp-to-ui, fp-to-si, ui-to-fp, si-to-fp (f32.to.i32, i32.to.f64, etc.)
  deriving (Eq, Show)

asUnaryOpMaybe :: T.Text -> Maybe UnaryOp
asUnaryOpMaybe name
  | [typeStr, "neg"] <- wordsBy '.' name
  , Just lowType <- asLowTypeMaybe typeStr = Just $ UnaryOpNeg lowType
asUnaryOpMaybe name
  | [domTypeStr, convOpStr, codTypeStr] <- wordsBy '.' name
  , Just domType <- asLowTypeMaybe domTypeStr
  , Just codType <- asLowTypeMaybe codTypeStr
  , Just op <- asConvOpMaybe domType codType convOpStr = Just op
asUnaryOpMaybe _ = Nothing

unaryOpToDomCod :: UnaryOp -> (LowType, LowType)
unaryOpToDomCod (UnaryOpNeg t) = (t, t)
unaryOpToDomCod (UnaryOpTrunc dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpZext dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpSext dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpFpExt dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpTo dom cod) = (dom, cod)

asConvOpMaybe :: LowType -> LowType -> T.Text -> Maybe UnaryOp
asConvOpMaybe domType codType "trunc" = Just $ UnaryOpTrunc domType codType
asConvOpMaybe domType codType "zext" = Just $ UnaryOpZext domType codType
asConvOpMaybe domType codType "sext" = Just $ UnaryOpSext domType codType
asConvOpMaybe domType codType "ext" = Just $ UnaryOpFpExt domType codType
asConvOpMaybe domType codType "to" = Just $ UnaryOpTo domType codType
asConvOpMaybe _ _ _ = Nothing

data BinaryOp
  = BinaryOpAdd LowType -- (X, X) -> X
  | BinaryOpSub LowType -- (X, X) -> X
  | BinaryOpMul LowType -- (X, X) -> X
  | BinaryOpDiv LowType -- (X, X) -> X
  | BinaryOpRem LowType -- (X, X) -> X
  | BinaryOpEQ LowType -- (X, X) -> bool
  | BinaryOpNE LowType -- (X, X) -> bool
  | BinaryOpGT LowType -- (X, X) -> bool
  | BinaryOpGE LowType -- (X, X) -> bool
  | BinaryOpLT LowType -- (X, X) -> bool
  | BinaryOpLE LowType -- (X, X) -> bool
  | BinaryOpShl LowType -- (X, X) -> X
  | BinaryOpLshr LowType -- (X, X) -> X
  | BinaryOpAshr LowType -- (X, X) -> X
  | BinaryOpAnd LowType -- (X, X) -> X
  | BinaryOpOr LowType -- (X, X) -> X
  | BinaryOpXor LowType -- (X, X) -> X
  deriving (Eq, Show)

asBinaryOpMaybe :: T.Text -> Maybe BinaryOp
asBinaryOpMaybe name
  | [typeStr, opStr] <- wordsBy '.' name -- e.g. name == "i8.add"
  , Just lowType <- asLowTypeMaybe typeStr
  , Just f <- asBinaryOpMaybe' opStr = Just $ f lowType
asBinaryOpMaybe _ = Nothing

binaryOpToDomCod :: BinaryOp -> (LowType, LowType)
binaryOpToDomCod (BinaryOpAdd t) = (t, t)
binaryOpToDomCod (BinaryOpSub t) = (t, t)
binaryOpToDomCod (BinaryOpMul t) = (t, t)
binaryOpToDomCod (BinaryOpDiv t) = (t, t)
binaryOpToDomCod (BinaryOpRem t) = (t, t)
binaryOpToDomCod (BinaryOpEQ t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpNE t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpGT t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpGE t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpLT t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpLE t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpShl t) = (t, t)
binaryOpToDomCod (BinaryOpLshr t) = (t, t)
binaryOpToDomCod (BinaryOpAshr t) = (t, t)
binaryOpToDomCod (BinaryOpAnd t) = (t, t)
binaryOpToDomCod (BinaryOpOr t) = (t, t)
binaryOpToDomCod (BinaryOpXor t) = (t, t)

asBinaryOpMaybe' :: T.Text -> Maybe (LowType -> BinaryOp)
asBinaryOpMaybe' "add" = Just BinaryOpAdd
asBinaryOpMaybe' "sub" = Just BinaryOpSub
asBinaryOpMaybe' "mul" = Just BinaryOpMul
asBinaryOpMaybe' "div" = Just BinaryOpDiv
asBinaryOpMaybe' "rem" = Just BinaryOpRem
asBinaryOpMaybe' "eq" = Just BinaryOpEQ
asBinaryOpMaybe' "ne" = Just BinaryOpNE
asBinaryOpMaybe' "gt" = Just BinaryOpGT
asBinaryOpMaybe' "ge" = Just BinaryOpGE
asBinaryOpMaybe' "lt" = Just BinaryOpLT
asBinaryOpMaybe' "le" = Just BinaryOpLE
asBinaryOpMaybe' "shl" = Just BinaryOpShl
asBinaryOpMaybe' "lshr" = Just BinaryOpLshr
asBinaryOpMaybe' "ashr" = Just BinaryOpAshr
asBinaryOpMaybe' "and" = Just BinaryOpAnd
asBinaryOpMaybe' "or" = Just BinaryOpOr
asBinaryOpMaybe' "xor" = Just BinaryOpXor
asBinaryOpMaybe' _ = Nothing

type Target = (OS, Arch)

data OS
  = OSLinux
  | OSDarwin
  deriving (Eq, Show)

showOS :: OS -> T.Text
showOS OSLinux = "linux"
showOS OSDarwin = "darwin"

data Arch =
  Arch64
  deriving (Eq, Show)

showArch :: Arch -> T.Text
showArch Arch64 = "x64"

-- Left name-of-interface-function | Right (name-of-syscall, number-of-syscall)
-- the `Left` here is required since direct use of syscall in macOS is deprecated since 10.12, and thus we need to
-- use corresponding interface functions.
type Syscall = Either T.Text (T.Text, Integer)

linearCheck :: (Eq a, Ord a) => [a] -> Bool
linearCheck xs = linearCheck' S.empty xs

linearCheck' :: (Eq a, Ord a) => (S.Set a) -> [a] -> Bool
linearCheck' _ [] = True
linearCheck' found (x:_)
  | x `S.member` found = False
linearCheck' found (x:xs) = linearCheck' (S.insert x found) xs

wordsBy :: Char -> T.Text -> [T.Text]
wordsBy c s =
  case T.dropWhile (== c) s of
    "" -> []
    s' -> do
      let (w, s'') = T.break (== c) s'
      w : wordsBy c s''

splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast [x] = return ([], x)
splitLast (x:xs) = do
  (xs', z) <- splitLast xs
  return (x : xs', z)
