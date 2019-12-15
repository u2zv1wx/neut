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

data Arith
  = ArithAdd
  | ArithSub
  | ArithMul
  | ArithDiv
  deriving (Show)

intLowTypeList :: [LowType]
intLowTypeList = signedIntLowTypeList ++ unsignedIntLowTypeList

signedIntLowTypeList :: [LowType]
signedIntLowTypeList =
  [ LowTypeSignedInt 1
  , LowTypeSignedInt 2
  , LowTypeSignedInt 4
  , LowTypeSignedInt 8
  , LowTypeSignedInt 16
  , LowTypeSignedInt 32
  , LowTypeSignedInt 64
  ]

unsignedIntLowTypeList :: [LowType]
unsignedIntLowTypeList =
  [ LowTypeUnsignedInt 1
  , LowTypeUnsignedInt 2
  , LowTypeUnsignedInt 4
  , LowTypeUnsignedInt 8
  , LowTypeUnsignedInt 16
  , LowTypeUnsignedInt 32
  , LowTypeUnsignedInt 64
  ]

intAddConstantList :: [String]
intAddConstantList =
  flip map intLowTypeList $ \t -> "core." ++ showLowType t ++ ".add"

intSubConstantList :: [String]
intSubConstantList =
  flip map intLowTypeList $ \t -> "core." ++ showLowType t ++ ".sub"

intMulConstantList :: [String]
intMulConstantList =
  flip map intLowTypeList $ \t -> "core." ++ showLowType t ++ ".mul"

intDivConstantList :: [String]
intDivConstantList =
  flip map intLowTypeList $ \t -> "core." ++ showLowType t ++ ".div"

intArithConstantList :: [String]
intArithConstantList =
  intAddConstantList ++
  intSubConstantList ++ intMulConstantList ++ intDivConstantList

floatLowTypeList :: [LowType]
floatLowTypeList = [LowTypeFloat 16, LowTypeFloat 32, LowTypeFloat 64]

floatAddConstantList :: [String]
floatAddConstantList =
  flip map floatLowTypeList $ \t -> "core." ++ showLowType t ++ ".add"

floatSubConstantList :: [String]
floatSubConstantList =
  flip map floatLowTypeList $ \t -> "core." ++ showLowType t ++ ".sub"

floatMulConstantList :: [String]
floatMulConstantList =
  flip map floatLowTypeList $ \t -> "core." ++ showLowType t ++ ".mul"

floatDivConstantList :: [String]
floatDivConstantList =
  flip map floatLowTypeList $ \t -> "core." ++ showLowType t ++ ".div"

floatArithConstantList :: [String]
floatArithConstantList =
  floatAddConstantList ++
  floatSubConstantList ++ floatMulConstantList ++ floatDivConstantList

showLowType :: LowType -> String
showLowType (LowTypeSignedInt i) = "i" ++ show i
showLowType (LowTypeUnsignedInt i) = "u" ++ show i
showLowType (LowTypeFloat i) = "f" ++ show i -- shouldn't occur
showLowType (LowTypePointer t) = showLowType t ++ "*"
showLowType (LowTypeStruct ts) = "{" ++ showItems showLowType ts ++ "}"
showLowType (LowTypeFunction ts t) =
  showLowType t ++ " (" ++ showItems showLowType ts ++ ")"

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
