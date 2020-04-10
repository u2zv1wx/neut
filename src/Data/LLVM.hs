module Data.LLVM where

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Basic

data LLVMData
  = LLVMDataLocal Identifier
  | LLVMDataGlobal T.Text
  | LLVMDataInt Integer
  | LLVMDataFloat FloatSize Double
  | LLVMDataNull
  deriving (Show)

data LLVM
  = LLVMReturn LLVMData -- UpIntro
  | LLVMLet Identifier LLVMOp LLVM -- UpElim
  | LLVMCont LLVMOp LLVM -- LLVMLet that discards the result of LLVMOp
  | LLVMSwitch (LLVMData, LowType) LLVM [(Int, LLVM)] -- EnumElim
  | LLVMBranch LLVMData LLVM LLVM
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
  | LLVMOpAlloc LLVMData SizeInfo
  | LLVMOpFree LLVMData SizeInfo Int -- (var, size-of-var, name-of-free)   (name-of-free is only for optimization)
  | LLVMOpUnaryOp UnaryOp LLVMData
  | LLVMOpBinaryOp BinaryOp LLVMData LLVMData
  | LLVMOpSysCall
      Integer -- syscall number
      [LLVMData] -- arguments
  deriving (Show)

type SizeInfo = LowType

type SubstLLVM = IntMap.IntMap LLVMData

substLLVMData :: SubstLLVM -> LLVMData -> LLVMData
substLLVMData sub (LLVMDataLocal x) =
  case IntMap.lookup (asInt x) sub of
    Just d -> d
    Nothing -> LLVMDataLocal x
substLLVMData _ d = d

substLLVMOp :: SubstLLVM -> LLVMOp -> LLVMOp
substLLVMOp sub (LLVMOpCall d ds) = do
  let d' = substLLVMData sub d
  let ds' = map (substLLVMData sub) ds
  LLVMOpCall d' ds'
substLLVMOp sub (LLVMOpGetElementPtr (d, t) dts) = do
  let d' = substLLVMData sub d
  let (ds, ts) = unzip dts
  let ds' = map (substLLVMData sub) ds
  LLVMOpGetElementPtr (d', t) (zip ds' ts)
substLLVMOp sub (LLVMOpBitcast d t1 t2) = do
  let d' = substLLVMData sub d
  LLVMOpBitcast d' t1 t2
substLLVMOp sub (LLVMOpIntToPointer d t1 t2) = do
  let d' = substLLVMData sub d
  LLVMOpIntToPointer d' t1 t2
substLLVMOp sub (LLVMOpPointerToInt d t1 t2) = do
  let d' = substLLVMData sub d
  LLVMOpPointerToInt d' t1 t2
substLLVMOp sub (LLVMOpLoad d t) = do
  let d' = substLLVMData sub d
  LLVMOpLoad d' t
substLLVMOp sub (LLVMOpStore t d1 d2) = do
  let d1' = substLLVMData sub d1
  let d2' = substLLVMData sub d2
  LLVMOpStore t d1' d2'
substLLVMOp sub (LLVMOpAlloc d sizeInfo) = do
  let d' = substLLVMData sub d
  LLVMOpAlloc d' sizeInfo
substLLVMOp sub (LLVMOpFree d sizeInfo i) = do
  let d' = substLLVMData sub d
  LLVMOpFree d' sizeInfo i
substLLVMOp sub (LLVMOpUnaryOp op d) = do
  let d' = substLLVMData sub d
  LLVMOpUnaryOp op d'
substLLVMOp sub (LLVMOpBinaryOp op d1 d2) = do
  let d1' = substLLVMData sub d1
  let d2' = substLLVMData sub d2
  LLVMOpBinaryOp op d1' d2'
substLLVMOp sub (LLVMOpSysCall i ds) = do
  let ds' = map (substLLVMData sub) ds
  LLVMOpSysCall i ds'
