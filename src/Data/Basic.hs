{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.Basic where

import Data.Hashable
import GHC.Generics (Generic)
import Path

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

import Data.Bits
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

asIdent :: T.Text -> Identifier
asIdent s = I (s, 0)

asInt :: Identifier -> Int
asInt (I (_, i)) = i

instance Show Identifier where
  show (I (s, i)) = T.unpack s ++ "-" ++ show i

-- instance Eq Identifier where
--   (I (_, i1)) == (I (_, i2)) = i1 == i2
-- instance Ord Identifier where
--   compare (I (_, i1)) (I (_, i2)) = compare i1 i2
data Case
  = CaseValue EnumValue
  | CaseDefault
  deriving (Show, Eq, Ord)

-- note that UnivLevel is just a name of the level of a universe (i.e. the integer
-- itself is not the level of the universe)
type UnivLevel = Int

newtype UnivLevelPlus =
  UnivLevelPlus (Meta, UnivLevel)

instance Show UnivLevelPlus where
  show (UnivLevelPlus (_, l)) = "[" ++ show l ++ "]"
  -- show (UnivLevelPlus (m, l)) = "[" ++ show l ++ "]:" ++ showMeta m

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
    , metaIsPublic = True
    , metaIsAppropriateAsCompletionCandidate = True
    , metaUnivParams = IntMap.empty
    }

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
  | EnumTypeNat Int -- n{k}
  deriving (Show, Eq)

data EnumValue
  = EnumValueIntS IntSize Integer
  | EnumValueIntU IntSize Integer
  | EnumValueNat Int Int
  | EnumValueLabel T.Text
  deriving (Show, Eq, Ord)

data LowType
  = LowTypeIntS IntSize
  | LowTypeIntU IntSize
  | LowTypeIntPtrS IntSize
  | LowTypeIntPtrU IntSize
  | LowTypeFloat FloatSize
  | LowTypeFloatPtr FloatSize
  | LowTypeVoidPtr
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStructPtr [LowType]
  | LowTypeArrayPtr Int LowType -- [n x LOWTYPE]*
  | LowTypeIntS64Ptr
  deriving (Eq, Show)

asLowType :: Identifier -> LowType
asLowType (I (n, _)) = fromMaybe (LowTypeIntS 64) (asLowTypeMaybe n)

asLowTypeMaybe :: T.Text -> Maybe LowType
asLowTypeMaybe "" = Nothing
asLowTypeMaybe s
  | 'i' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n < (2 ^ (23 :: Int)) - 1 = Just $ LowTypeIntS n
asLowTypeMaybe s
  | 'u' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n < (2 ^ (23 :: Int)) - 1 = Just $ LowTypeIntU n
asLowTypeMaybe s
  | 'f' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , Just size <- asFloatSize n = Just $ LowTypeFloat size
asLowTypeMaybe _ = Nothing

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

data UnaryOp
  = UnaryOpNeg -- fneg
  | UnaryOpTrunc LowType -- trunc, fptrunc
  | UnaryOpZext LowType -- zext
  | UnaryOpSext LowType -- sext
  | UnaryOpFpExt LowType -- fpext
  | UnaryOpTo LowType -- fp-to-ui, fp-to-si, ui-to-fp, si-to-fp (f32.to.i32, i32.to.f64, etc.)
  deriving (Eq, Show)

asUnaryOpMaybe :: T.Text -> Maybe (LowType, UnaryOp)
asUnaryOpMaybe name
  | [typeStr, "neg"] <- wordsBy '.' name
  , Just lowType <- asLowTypeMaybe typeStr = Just (lowType, UnaryOpNeg)
asUnaryOpMaybe name
  | [domTypeStr, convOpStr, codTypeStr] <- wordsBy '.' name
  , Just domType <- asLowTypeMaybe domTypeStr
  , Just codType <- asLowTypeMaybe codTypeStr
  , Just op <- asConvOpMaybe codType convOpStr = Just (domType, op)
asUnaryOpMaybe _ = Nothing

asConvOpMaybe :: LowType -> T.Text -> Maybe UnaryOp
asConvOpMaybe codType "trunc" = Just $ UnaryOpTrunc codType
asConvOpMaybe codType "zext" = Just $ UnaryOpZext codType
asConvOpMaybe codType "sext" = Just $ UnaryOpSext codType
asConvOpMaybe codType "ext" = Just $ UnaryOpFpExt codType
asConvOpMaybe codType "to" = Just $ UnaryOpTo codType
asConvOpMaybe _ _ = Nothing

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

asBinaryOpMaybe :: T.Text -> Maybe (LowType, BinaryOp)
asBinaryOpMaybe name
  | [typeStr, opStr] <- wordsBy '.' name -- e.g. name == "i8.add"
  , Just lowType <- asLowTypeMaybe typeStr
  , Just op <- asBinaryOpMaybe' opStr = Just (lowType, op)
asBinaryOpMaybe _ = Nothing

asBinaryOpMaybe' :: T.Text -> Maybe BinaryOp
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

type Target = (OS, Arch)

data OS
  = OSLinux
  | OSDarwin
  deriving (Eq, Show)

data Arch =
  Arch64
  deriving (Eq, Show)

-- {} linearCheck {}
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
