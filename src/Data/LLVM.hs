module Data.LLVM where

import Numeric.Half

import Data.Basic

data LLVMData
  = LLVMDataLocal Identifier
  | LLVMDataGlobal Identifier
  | LLVMDataInt IntSize Integer
  | LLVMDataFloat16 Half
  | LLVMDataFloat32 Float
  | LLVMDataFloat64 Double
  deriving (Show)

data LLVM
  = LLVMReturn LLVMData -- UpIntro
  | LLVMLet Identifier LLVMOp LLVM -- UpElim
  | LLVMCont LLVMOp LLVM -- LLVMLet that discards the result of LLVMOp
  | LLVMSwitch (LLVMData, LowType) LLVM [(Int, LLVM)] -- EnumElim
  | LLVMCall LLVMData [LLVMData]
  | LLVMUnreachable -- for empty case analysis
  deriving (Show)

data LLVMOp
  = LLVMOpCall LLVMData [LLVMData]
  | LLVMOpGetElementPtr
      (LLVMData, LowType) -- (base pointer, the type of base pointer)
      LLVMData -- index
  | LLVMOpBitcast
      LLVMData
      LowType -- cast from
      LowType -- cast to
  | LLVMOpIntToPointer LLVMData LowType LowType
  | LLVMOpPointerToInt LLVMData LowType LowType
  | LLVMOpLoad LLVMData LowType
  | LLVMOpStore LowType LLVMData LLVMData
  | LLVMOpAlloc AllocSize
  | LLVMOpFree LLVMData
  | LLVMOpUnaryOp (UnaryOp, LowType) LLVMData
  | LLVMOpBinaryOp (BinaryOp, LowType) LLVMData LLVMData
  | LLVMOpPrint LowType LLVMData
  deriving (Show)

data AllocSize
  = AllocSizeExact Int
  | AllocSizePtrList Int
  deriving (Show)

-- commutative conversion
commConv :: Identifier -> LLVM -> LLVM -> LLVM
commConv x (LLVMReturn d) cont =
  LLVMLet x (LLVMOpBitcast d voidPtr voidPtr) cont -- nop
commConv x (LLVMLet y op cont1) cont2 = LLVMLet y op $ commConv x cont1 cont2
commConv x (LLVMCont op cont1) cont2 = LLVMCont op $ commConv x cont1 cont2
commConv x (LLVMSwitch (d, t) defaultCase caseList) cont2 = do
  let (ds, es) = unzip caseList
  let es' = map (\e -> commConv x e cont2) es
  let caseList' = zip ds es'
  let defaultCase' = commConv x defaultCase cont2
  LLVMSwitch (d, t) defaultCase' caseList'
commConv x (LLVMCall d ds) cont2 = LLVMLet x (LLVMOpCall d ds) cont2
commConv _ LLVMUnreachable _ = LLVMUnreachable

showLLVMData :: LLVMData -> String
showLLVMData (LLVMDataLocal x) = "%" ++ x
showLLVMData (LLVMDataGlobal x) = "@" ++ x
showLLVMData (LLVMDataInt _ i) = show i
showLLVMData (LLVMDataFloat16 x) = show x
showLLVMData (LLVMDataFloat32 x) = show x
showLLVMData (LLVMDataFloat64 x) = show x
