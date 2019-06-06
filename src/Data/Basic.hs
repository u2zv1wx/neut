module Data.Basic where

type Identifier = String

data Index
  = IndexLabel Identifier
  | IndexInteger Int
  | IndexFloat Double
  | IndexDefault
  deriving (Show, Eq)

data LowType
  = LowTypeSignedInt Int
  | LowTypeUnsignedInt Int
  | LowTypeFloat Int
  | LowTypePointer LowType
  | LowTypeFunction [LowType]
                    LowType
  | LowTypeArray Int
                 LowType
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

data UnivLevel
  = UnivLevelHole Identifier
  | UnivLevelNext UnivLevel
  deriving (Show, Eq)

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

floatLowTypeList :: [LowType]
floatLowTypeList = [LowTypeFloat 16, LowTypeFloat 32, LowTypeFloat 64]

intAddConstantList :: [String]
intAddConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".add"

intSubConstantList :: [String]
intSubConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".sub"

intMulConstantList :: [String]
intMulConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".mul"

intDivConstantList :: [String]
intDivConstantList = flip map intLowTypeList $ \t -> "core." ++ show t ++ ".div"
