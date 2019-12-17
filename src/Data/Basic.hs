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

data BinOp
  = BinOpAdd
  | BinOpSub
  | BinOpMul
  | BinOpDiv
  | BinOpEQ
  | BinOpNE
  | BinOpGT
  | BinOpGE
  | BinOpLT
  | BinOpLE
  deriving (Eq, Show)

arithOpList :: [BinOp]
arithOpList = [BinOpAdd, BinOpSub, BinOpMul, BinOpDiv]

compareOpList :: [BinOp]
compareOpList = [BinOpEQ, BinOpNE, BinOpGT, BinOpGE, BinOpLT, BinOpLE]

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

asBinOpMaybe :: Identifier -> Maybe BinOp
asBinOpMaybe "add" = Just BinOpAdd
asBinOpMaybe "sub" = Just BinOpSub
asBinOpMaybe "mul" = Just BinOpMul
asBinOpMaybe "div" = Just BinOpDiv
asBinOpMaybe "eq" = Just BinOpEQ
asBinOpMaybe "ne" = Just BinOpNE
asBinOpMaybe "gt" = Just BinOpGT
asBinOpMaybe "ge" = Just BinOpGE
asBinOpMaybe "lt" = Just BinOpLT
asBinOpMaybe "le" = Just BinOpLE
asBinOpMaybe _ = Nothing

wordsBy :: Char -> String -> [String]
wordsBy c s =
  case dropWhile (== c) s of
    "" -> []
    s' -> do
      let (w, s'') = break (== c) s'
      w : wordsBy c s''
