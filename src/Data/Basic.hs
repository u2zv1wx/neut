module Data.Basic where

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

data UnaryOp =
  UnaryOpNeg
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
  deriving (Eq, Show)

arithOpList :: [BinaryOp]
arithOpList = [BinaryOpAdd, BinaryOpSub, BinaryOpMul, BinaryOpDiv, BinaryOpRem]

compareOpList :: [BinaryOp]
compareOpList =
  [BinaryOpEQ, BinaryOpNE, BinaryOpGT, BinaryOpGE, BinaryOpLT, BinaryOpLE]

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

asUnaryOpMaybe :: Identifier -> Maybe UnaryOp
asUnaryOpMaybe "neg" = Just UnaryOpNeg
asUnaryOpMaybe _ = Nothing

asBinaryOpMaybe :: Identifier -> Maybe BinaryOp
asBinaryOpMaybe "add" = Just BinaryOpAdd
asBinaryOpMaybe "sub" = Just BinaryOpSub
asBinaryOpMaybe "mul" = Just BinaryOpMul
asBinaryOpMaybe "div" = Just BinaryOpDiv
asBinaryOpMaybe "rem" = Just BinaryOpRem
asBinaryOpMaybe "eq" = Just BinaryOpEQ
asBinaryOpMaybe "ne" = Just BinaryOpNE
asBinaryOpMaybe "gt" = Just BinaryOpGT
asBinaryOpMaybe "ge" = Just BinaryOpGE
asBinaryOpMaybe "lt" = Just BinaryOpLT
asBinaryOpMaybe "le" = Just BinaryOpLE
asBinaryOpMaybe _ = Nothing

wordsBy :: Char -> String -> [String]
wordsBy c s =
  case dropWhile (== c) s of
    "" -> []
    s' -> do
      let (w, s'') = break (== c) s'
      w : wordsBy c s''
