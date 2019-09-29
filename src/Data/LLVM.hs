module Data.LLVM where

import Data.Basic

data LLVMData
  = LLVMDataLocal Identifier
  | LLVMDataGlobal Identifier
  | LLVMDataStruct [LLVMData]
  | LLVMDataInt Int Int
  | LLVMDataFloat Double Int
  deriving (Show)

data LLVM
  = LLVMCall
      LLVMData -- PiElimDownElim
      [LLVMData]
  | LLVMSwitch
      LLVMData -- IndexElim
      LLVM
      [(Int, LLVM)]
  | LLVMReturn LLVMData -- UpIntro
  | LLVMLet
      Identifier -- UpElim
      LLVM
      LLVM
  | LLVMGetElementPtr LLVMData Loc -- (index, length)
  | LLVMBitcast LLVMData LowType LowType -- cast to this type
  | LLVMIntToPointer LLVMData LowType LowType
  | LLVMPointerToInt LLVMData LowType LowType
  | LLVMLoad LLVMData
  | LLVMStore (LLVMData, LowType) (LLVMData, LowType)
  | LLVMAlloc Int
  | LLVMFree LLVMData
  | LLVMArith (Arith, LowType) LLVMData LLVMData
  | LLVMPrint LowType LLVMData
  deriving (Show)
