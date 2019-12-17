module Data.Basic where

import Data.Bits

type Identifier = String

type Loc = (Int, Int)

data Case
  = CaseLabel Identifier
  | CaseDefault
  deriving (Show, Eq)

data LowType
  = LowTypeSignedInt Int
  | LowTypeUnsignedInt Int
  | LowTypeFloat Int
  | LowTypePointer LowType
  | LowTypeFunction [LowType] LowType
  | LowTypeStruct [LowType]
  deriving (Eq, Show)

voidPtr :: LowType
voidPtr = LowTypePointer $ LowTypeSignedInt 8

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
asLowType ('i':cs)
  | Just n <- read cs = LowTypeSignedInt n
asLowType ('u':cs)
  | Just n <- read cs = LowTypeUnsignedInt n
asLowType ('f':cs)
  | Just n <- read cs = LowTypeFloat n
asLowType _ = LowTypeSignedInt 64 -- labels are i64

asLowTypeMaybe :: Identifier -> Maybe LowType
asLowTypeMaybe ('i':cs)
  | Just n <- read cs = Just $ LowTypeSignedInt n
asLowTypeMaybe ('u':cs)
  | Just n <- read cs = Just $ LowTypeUnsignedInt n
asLowTypeMaybe ('f':cs)
  | Just n <- read cs = Just $ LowTypeFloat n
asLowTypeMaybe _ = Nothing

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
