module Data.Basic where

import Data.Bits
import Data.Maybe (fromMaybe)

type Identifier = String

type Loc = (Int, Int)

type EpsilonLabel = Identifier

data Case
  = CaseLabel Identifier
  | CaseDefault
  deriving (Show, Eq)

data LowType
  = LowTypeIntS IntSize
  | LowTypeIntU IntSize
  | LowTypeFloat FloatSize
  | LowTypeVoidPtr
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStructPtr [LowType]
  | LowTypeArrayPtr Int LowType -- [n x LOWTYPE]*
  deriving (Eq, Show)

type IntSize = Int

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

sizeAsInt :: FloatSize -> Int
sizeAsInt FloatSize16 = 16
sizeAsInt FloatSize32 = 32
sizeAsInt FloatSize64 = 64

data ArrayKind
  = ArrayKindIntS Int
  | ArrayKindIntU Int
  | ArrayKindFloat FloatSize
  deriving (Show, Eq)

asArrayKind :: LowType -> Maybe ArrayKind
asArrayKind (LowTypeIntS i) = Just $ ArrayKindIntS i
asArrayKind (LowTypeIntU i) = Just $ ArrayKindIntU i
asArrayKind (LowTypeFloat size) = Just $ ArrayKindFloat size
asArrayKind _ = Nothing

arrayKindToLowType :: ArrayKind -> LowType
arrayKindToLowType (ArrayKindIntS i) = LowTypeIntS i
arrayKindToLowType (ArrayKindIntU i) = LowTypeIntU i
arrayKindToLowType (ArrayKindFloat size) = LowTypeFloat size

voidPtr :: LowType
-- voidPtr = LowTypePointer $ LowTypeIntS 8
voidPtr = LowTypeVoidPtr

data UnaryOp
  = UnaryOpNeg -- fneg
  | UnaryOpTrunc LowType -- trunc, fptrunc
  | UnaryOpZext LowType -- zext
  | UnaryOpSext LowType -- sext
  | UnaryOpFpExt LowType -- fpext
  | UnaryOpTo LowType -- fp-to-ui, fp-to-si, ui-to-fp, si-to-fp (f32.to.i32, i32.to.f64, etc.)
  deriving (Eq, Show)

getCodType :: UnaryOp -> Maybe LowType
getCodType (UnaryOpTrunc lowType) = Just lowType
getCodType (UnaryOpZext lowType) = Just lowType
getCodType (UnaryOpSext lowType) = Just lowType
getCodType (UnaryOpFpExt lowType) = Just lowType
getCodType (UnaryOpTo lowType) = Just lowType
getCodType _ = Nothing

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

isArithOp :: BinaryOp -> Bool
isArithOp BinaryOpAdd = True
isArithOp BinaryOpSub = True
isArithOp BinaryOpMul = True
isArithOp BinaryOpDiv = True
isArithOp BinaryOpRem = True
isArithOp BinaryOpShl = True
isArithOp BinaryOpLshr = True
isArithOp BinaryOpAshr = True
isArithOp BinaryOpAnd = True
isArithOp BinaryOpOr = True
isArithOp BinaryOpXor = True
isArithOp _ = False

isCompareOp :: BinaryOp -> Bool
isCompareOp BinaryOpEQ = True
isCompareOp BinaryOpNE = True
isCompareOp BinaryOpGT = True
isCompareOp BinaryOpGE = True
isCompareOp BinaryOpLT = True
isCompareOp BinaryOpLE = True
isCompareOp _ = False

showItems :: (a -> String) -> [a] -> String
showItems _ [] = ""
showItems f [a] = f a
showItems f (a:as) = f a ++ ", " ++ showItems f as

asLowType :: Identifier -> LowType
asLowType n = fromMaybe (LowTypeIntS 64) (asLowTypeMaybe n)

asLowTypeMaybe :: Identifier -> Maybe LowType
asLowTypeMaybe ('i':cs)
  | Just n <- read cs = Just $ LowTypeIntS n
asLowTypeMaybe ('u':cs)
  | Just n <- read cs = Just $ LowTypeIntU n
asLowTypeMaybe ('f':cs)
  | Just n <- read cs
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

wordsBy :: Char -> String -> [String]
wordsBy c s =
  case dropWhile (== c) s of
    "" -> []
    s' -> do
      let (w, s'') = break (== c) s'
      w : wordsBy c s''

ushiftR :: Int -> Int -> Int
ushiftR n k = fromIntegral (fromIntegral n `shiftR` k :: Word)

ushiftR' :: (Integral a) => a -> Int -> a
ushiftR' n k = fromIntegral (fromIntegral n `shiftR` k :: Word)
