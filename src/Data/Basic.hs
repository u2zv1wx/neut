{-# LANGUAGE OverloadedStrings #-}

module Data.Basic where

import Path

import qualified Data.Text as T

-- import Control.Exception (assert)
import Data.Bits
import Data.Maybe (fromMaybe)
import Text.Read

type Identifier = T.Text

type Phase = Integer

type Line = Integer

type Column = Integer

type Loc = (Phase, Line, Column)

data Case
  = CaseValue EnumValue
  | CaseDefault
  deriving (Show, Eq, Ord)

data EnumType
  = EnumTypeLabel Identifier
  | EnumTypeIntS Integer -- i{k}
  | EnumTypeIntU Integer -- u{k}
  | EnumTypeNat Integer -- n{k}
  deriving (Show, Eq)

data Meta =
  Meta
    { metaFileName :: Maybe (Path Abs File)
    , metaLocation :: Maybe Loc
    , metaConstraintLocation :: Maybe Loc
    }

-- required to derive the eqality on WeakTerm
instance Eq Meta where
  _ == _ = True

instance Show Meta where
  show _ = "_"

showMeta :: Meta -> String
showMeta m =
  case (metaFileName m, metaConstraintLocation m) of
    (Just name, Nothing) -> toFilePath name
    -- (Just name, Just (_, l,))
    --   | (_, l, c) <- minimum xs ->
    --     toFilePath name ++ ":" ++ show l ++ ":" ++ show c
    (Just name, Just (_, l, c)) ->
      toFilePath name ++ ":" ++ show l ++ ":" ++ show c
    (Nothing, Nothing) -> "_"
    (Nothing, Just (_, l, c)) -> "<unknown-file>:" ++ show l ++ ":" ++ show c
    -- (Nothing, xs)
    --   | (_, l, c) <- minimum xs -> "<unknown-file>:" ++ show l ++ ":" ++ show c

showMeta' :: Meta -> String
showMeta' m =
  case (metaFileName m, metaConstraintLocation m) of
    (Just name, Nothing) -> toFilePath name
    (Just name, Just (ph, l, c)) ->
      toFilePath name ++ ":" ++ show ph ++ ":" ++ show l ++ ":" ++ show c
    (Nothing, Nothing) -> "_"
    (Nothing, Just (ph, l, c)) ->
      "<unknown-file>:" ++ show ph ++ ":" ++ show l ++ ":" ++ show c
    -- (Nothing, xs)
    --   | (_, l, c) <- minimum xs -> "<unknown-file>:" ++ show l ++ ":" ++ show c

supMeta :: Meta -> Meta -> Meta
supMeta m1 m2
  | metaConstraintLocation m1 < metaConstraintLocation m2 =
    m1 {metaConstraintLocation = metaConstraintLocation m2}
  | otherwise = m1

getInfo :: Meta -> Maybe (Path Abs File, Loc)
getInfo m =
  case (metaFileName m, metaLocation m) of
    (Just name, Just loc) -> return (name, loc)
    _ -> Nothing

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) = toFilePath path ++ ":" ++ show l ++ ":" ++ show c

emptyMeta :: Meta
emptyMeta =
  Meta
    { metaLocation = Nothing
    , metaConstraintLocation = Nothing
    , metaFileName = Nothing
    }

readEnumType :: Char -> Identifier -> Integer -> (Maybe Integer)
readEnumType c str k -- n1, n2, ..., n{i}, ..., n{2^64}
  | T.length str >= 2
  , T.head str == c
  , Just i <- readMaybe $ T.unpack $ T.tail str
  , 1 <= i && i <= 2 ^ k = Just i
readEnumType _ _ _ = Nothing

readEnumTypeNat :: Identifier -> (Maybe Integer)
readEnumTypeNat str = readEnumType 'n' str 64

readEnumTypeIntS :: Identifier -> (Maybe Integer)
readEnumTypeIntS str = readEnumType 'i' str 23

readEnumTypeIntU :: Identifier -> (Maybe Integer)
readEnumTypeIntU str = readEnumType 'u' str 23

data EnumValue
  = EnumValueIntS IntSize Integer
  | EnumValueIntU IntSize Integer
  | EnumValueNat Integer Integer
  | EnumValueLabel Identifier
  deriving (Show, Eq, Ord)

readEnumValueIntS :: Identifier -> Identifier -> Maybe EnumValue
readEnumValueIntS t x
  | Just (LowTypeIntS i) <- asLowTypeMaybe t
  , Just x' <- readMaybe $ T.unpack x = Just $ EnumValueIntS i x'
  | otherwise = Nothing

readEnumValueIntU :: Identifier -> Identifier -> Maybe EnumValue
readEnumValueIntU t x
  | Just (LowTypeIntU i) <- asLowTypeMaybe t
  , Just x' <- readMaybe $ T.unpack x = Just $ EnumValueIntU i x'
  | otherwise = Nothing

readEnumValueNat :: Identifier -> Maybe EnumValue
readEnumValueNat str -- n1-0, n2-0, n2-1, ...
  | T.length str >= 4
  , T.head str == 'n'
  , [iStr, jStr] <- wordsBy '-' (T.tail str)
  , Just i <- readMaybe $ T.unpack iStr
  , 1 <= i && i <= 2 ^ (64 :: Integer)
  , Just j <- readMaybe $ T.unpack jStr
  , 0 <= j && j <= i - 1 = Just $ EnumValueNat i j
  | otherwise = Nothing

asEnumNatConstant :: Identifier -> Maybe Integer
asEnumNatConstant x
  | T.length x >= 7 -- length "enum.n4" == 7
  , ["enum", y] <- wordsBy '.' x
  , Just i <- readEnumTypeNat y = Just i -- enum.n{i} is a constant
asEnumNatConstant _ = Nothing

isConstant :: Identifier -> Bool
isConstant x
  | Just _ <- asEnumNatConstant x = True
  | Just (LowTypeFloat _) <- asLowTypeMaybe x = True
  | Just _ <- asUnaryOpMaybe x = True
  | Just _ <- asBinaryOpMaybe x = True
  | otherwise = False

data LowType
  = LowTypeIntS IntSize
  | LowTypeIntU IntSize
  | LowTypeFloat FloatSize
  | LowTypeVoidPtr
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStructPtr [LowType]
  | LowTypeArrayPtr Integer LowType -- [n x LOWTYPE]*
  | LowTypeIntS64Ptr
  deriving (Eq, Show)

lowTypeToAllocSize' :: Integer -> Integer
lowTypeToAllocSize' i = do
  let (q, r) = quotRem i 8
  if r == 0
    then q
    else q + 1

type IntSize = Integer

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

data FloatSize
  = FloatSize16
  | FloatSize32
  | FloatSize64
  deriving (Eq, Show)

sizeAsInt :: FloatSize -> Integer
sizeAsInt FloatSize16 = 16
sizeAsInt FloatSize32 = 32
sizeAsInt FloatSize64 = 64

data ArrayKind
  = ArrayKindIntS Integer
  | ArrayKindIntU Integer
  | ArrayKindFloat FloatSize
  | ArrayKindVoidPtr
  deriving (Show, Eq)

asArrayKindMaybe :: LowType -> Maybe ArrayKind
asArrayKindMaybe (LowTypeIntS i) = Just $ ArrayKindIntS i
asArrayKindMaybe (LowTypeIntU i) = Just $ ArrayKindIntU i
asArrayKindMaybe (LowTypeFloat size) = Just $ ArrayKindFloat size
asArrayKindMaybe _ = Nothing

arrayKindToLowType :: ArrayKind -> LowType
arrayKindToLowType (ArrayKindIntS i) = LowTypeIntS i
arrayKindToLowType (ArrayKindIntU i) = LowTypeIntU i
arrayKindToLowType (ArrayKindFloat size) = LowTypeFloat size
arrayKindToLowType ArrayKindVoidPtr = LowTypeVoidPtr

voidPtr :: LowType
voidPtr = LowTypeVoidPtr

arrVoidPtr :: ArrayKind
arrVoidPtr = ArrayKindVoidPtr

data UnaryOp
  = UnaryOpNeg -- fneg
  | UnaryOpTrunc LowType -- trunc, fptrunc
  | UnaryOpZext LowType -- zext
  | UnaryOpSext LowType -- sext
  | UnaryOpFpExt LowType -- fpext
  | UnaryOpTo LowType -- fp-to-ui, fp-to-si, ui-to-fp, si-to-fp (f32.to.i32, i32.to.f64, etc.)
  deriving (Eq, Show)

data BinaryOp
  = BinaryOpAdd
  | BinaryOpSub
  | BinaryOpMul
  | BinaryOpDiv
  | BinaryOpRem
  | BinaryOpEQ
  | BinaryOpNE
  | BinaryOpGT
  | BinaryOpGE
  | BinaryOpLT
  | BinaryOpLE
  | BinaryOpShl
  | BinaryOpLshr
  | BinaryOpAshr
  | BinaryOpAnd
  | BinaryOpOr
  | BinaryOpXor
  deriving (Eq, Show)

data SysCall
  = SysCallWrite
  | SysCallRead
  | SysCallExit
  | SysCallOpen
  | SysCallClose
  | SysCallFork
  | SysCallSocket
  | SysCallListen
  | SysCallWait4
  | SysCallBind
  | SysCallAccept
  | SysCallConnect
  deriving (Eq, Show)

type ArgLen = Int

type UsedArgIndexList = [Int]

type Target = (OS, Arch)

data OS
  = OSLinux
  | OSDarwin
  deriving (Eq, Show)

data Arch =
  Arch64
  deriving (Eq, Show)

asLowType :: Identifier -> LowType
asLowType n = fromMaybe (LowTypeIntS 64) (asLowTypeMaybe n)

asLowTypeMaybe :: Identifier -> Maybe LowType
asLowTypeMaybe "" = Nothing
asLowTypeMaybe s
  | 'i' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n < (2 ^ (23 :: Integer)) - 1 = Just $ LowTypeIntS n
asLowTypeMaybe s
  | 'u' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n < (2 ^ (23 :: Integer)) - 1 = Just $ LowTypeIntU n
asLowTypeMaybe s
  | 'f' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , Just size <- asFloatSize n = Just $ LowTypeFloat size
asLowTypeMaybe _ = Nothing

asFloatSize :: Int -> Maybe FloatSize
asFloatSize 16 = Just FloatSize16
asFloatSize 32 = Just FloatSize32
asFloatSize 64 = Just FloatSize64
asFloatSize _ = Nothing

asUnaryOpMaybe :: Identifier -> Maybe (LowType, UnaryOp)
asUnaryOpMaybe name
  | [typeStr, "neg"] <- wordsBy '.' name
  , Just lowType <- asLowTypeMaybe typeStr = Just (lowType, UnaryOpNeg)
asUnaryOpMaybe name
  | [domTypeStr, convOpStr, codTypeStr] <- wordsBy '.' name
  , Just domType <- asLowTypeMaybe domTypeStr
  , Just codType <- asLowTypeMaybe codTypeStr
  , Just op <- asConvOpMaybe codType convOpStr = Just (domType, op)
asUnaryOpMaybe _ = Nothing

asConvOpMaybe :: LowType -> Identifier -> Maybe UnaryOp
asConvOpMaybe codType "trunc" = Just $ UnaryOpTrunc codType
asConvOpMaybe codType "zext" = Just $ UnaryOpZext codType
asConvOpMaybe codType "sext" = Just $ UnaryOpSext codType
asConvOpMaybe codType "ext" = Just $ UnaryOpFpExt codType
asConvOpMaybe codType "to" = Just $ UnaryOpTo codType
asConvOpMaybe _ _ = Nothing

asBinaryOpMaybe :: Identifier -> Maybe (LowType, BinaryOp)
asBinaryOpMaybe name
  | [typeStr, opStr] <- wordsBy '.' name -- e.g. name == "i8.add"
  , Just lowType <- asLowTypeMaybe typeStr
  , Just op <- asBinaryOpMaybe' opStr = Just (lowType, op)
asBinaryOpMaybe _ = Nothing

asBinaryOpMaybe' :: Identifier -> Maybe BinaryOp
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

wordsBy :: Char -> T.Text -> [T.Text]
wordsBy c s =
  case T.dropWhile (== c) s of
    "" -> []
    s' -> do
      let (w, s'') = T.break (== c) s'
      w : wordsBy c s''

-- sepAtLast '-' "array-access-u8" ~> ["array-access", "u8"]
sepAtLast :: Char -> T.Text -> [T.Text]
sepAtLast c s =
  case wordsBy c s of
    [] -> []
    [s'] -> [s']
    ss -> [T.intercalate (T.singleton c) (init ss), last ss]

ushiftR :: Int -> Int -> Int
ushiftR n k = fromIntegral (fromIntegral n `shiftR` k :: Word)

ushiftR' :: (Integral a) => a -> Int -> a
ushiftR' n k = fromIntegral (fromIntegral n `shiftR` k :: Word)

assert :: (Monad m) => String -> Bool -> a -> m a
assert str False _ = error str
assert _ True x = return x

-- `P` is for "Pure"
assertP :: String -> a -> Bool -> a
assertP str _ False = error str
assertP _ x True = x

-- assert-pure-monadic
assertPM :: (Monad m) => String -> a -> m Bool -> m a
assertPM msg x m = do
  b <- m
  assert msg b x

-- assert-unit-monadic
assertUM :: (Monad m) => String -> m Bool -> m ()
assertUM msg mb = do
  b <- mb
  assert msg b ()

-- assert-unit-pure
assertUP :: (Monad m) => String -> Bool -> m ()
assertUP msg b = assert msg b ()

-- assert-monadic-monadic
assertMM :: (Monad m) => String -> m a -> m Bool -> m a
assertMM msg mx mb = do
  b <- mb
  x <- mx
  assert msg b x

-- assert-monadic-pure
assertMP :: (Monad m) => String -> m a -> Bool -> m a
assertMP msg mx b = do
  x <- mx
  assert msg b x

assertPreUP :: (Monad m) => String -> Bool -> m ()
assertPreUP msg b = assertUP (msg ++ ".pre") b

assertPreUM :: (Monad m) => String -> m Bool -> m ()
assertPreUM msg mb = assertUM (msg ++ ".pre") mb

assertPostMM :: (Monad m) => String -> m a -> m Bool -> m a
assertPostMM msg mx mb = assertMM (msg ++ ".post") mx mb

assertPostMP :: (Monad m) => String -> m a -> Bool -> m a
assertPostMP msg mx b = assertMP (msg ++ ".post") mx b

assertPostPM :: (Monad m) => String -> a -> m Bool -> m a
assertPostPM msg x mb = assertPM (msg ++ ".post") x mb

splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast [x] = return ([], x)
splitLast (x:xs) = do
  (xs', z) <- splitLast xs
  return (x : xs', z)
