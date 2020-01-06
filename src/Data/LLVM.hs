module Data.LLVM where

import Numeric.Half

import Data.Basic

data LLVMData
  = LLVMDataLocal Identifier
  | LLVMDataGlobal Identifier
  | LLVMDataInt Integer
  | LLVMDataFloat16 Half
  | LLVMDataFloat32 Float
  | LLVMDataFloat64 Double
  | LLVMDataNull
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
      [(LLVMData, LowType)] -- [(index, the-typee-of-index)]
  | LLVMOpBitcast
      LLVMData
      LowType -- cast from
      LowType -- cast to
  | LLVMOpIntToPointer LLVMData LowType LowType
  | LLVMOpPointerToInt LLVMData LowType LowType
  | LLVMOpLoad LLVMData LowType
  | LLVMOpStore LowType LLVMData LLVMData
  | LLVMOpAlloc LLVMData -- size
  | LLVMOpFree LLVMData
  | LLVMOpUnaryOp (UnaryOp, LowType) LLVMData
  | LLVMOpBinaryOp (BinaryOp, LowType) LLVMData LLVMData
  | LLVMOpSysCall
      Integer -- syscall number
      [LLVMData] -- arguments
  deriving (Show)

data AllocSize
  = AllocSizeExact Integer
  | AllocSizePtrList Integer
  deriving (Show)
