module Data.LLVM where

import Numeric.Half

import Data.Basic

data LLVMData
  = LLVMDataLocal Identifier
  | LLVMDataGlobal Identifier
  | LLVMDataStruct [LLVMData]
  | LLVMDataIntS IntSize Integer
  | LLVMDataIntU IntSize Integer
  | LLVMDataFloat16 Half
  | LLVMDataFloat32 Float
  | LLVMDataFloat64 Double
  deriving (Show)

data LLVM
  = LLVMCall
      LLVMData -- PiElimDownElim
      [LLVMData]
  | LLVMSwitch
      (LLVMData, LowType) -- EpsilonElim
      LLVM
      [(Int, LLVM)]
  | LLVMReturn LLVMData -- UpIntro
  | LLVMLet
      Identifier -- UpElim
      LLVM
      LLVM
  | LLVMGetElementPtr
      (LLVMData, LowType) -- (base pointer, the type of base pointer)
      LLVMData -- index
  | LLVMBitcast LLVMData LowType LowType -- cast to this type
  | LLVMIntToPointer LLVMData LowType LowType
  | LLVMPointerToInt LLVMData LowType LowType
  | LLVMLoad LLVMData LowType
  | LLVMStore (LLVMData, LowType) (LLVMData, LowType)
  | LLVMAlloc AllocSize
  | LLVMFree LLVMData
  | LLVMUnaryOp (UnaryOp, LowType) LLVMData
  | LLVMBinaryOp (BinaryOp, LowType) LLVMData LLVMData
  | LLVMPrint LowType LLVMData
  | LLVMUnreachable -- for empty case analysis
  deriving (Show)

data AllocSize
  = AllocSizeExact Int
  | AllocSizePtrList Int
  deriving (Show)
