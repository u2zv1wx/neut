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
      (LLVMData, LowType) -- EpsilonElim
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
  | LLVMBinOp (BinOp, LowType) LLVMData LLVMData
  | LLVMPrint LowType LLVMData
  | LLVMUnreachable -- for empty case analysis
  deriving (Show)
