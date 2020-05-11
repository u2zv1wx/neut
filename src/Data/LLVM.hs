module Data.LLVM where

import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Primitive
import Data.Size
import qualified Data.Text as T

data LLVMData
  = LLVMDataLocal Ident
  | LLVMDataGlobal T.Text
  | LLVMDataInt Integer
  | LLVMDataFloat FloatSize Double
  | LLVMDataNull
  deriving (Show)

data LLVM
  = LLVMReturn LLVMData -- UpIntro
  | LLVMLet Ident LLVMOp LLVM -- UpElim
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
  | LLVMOpAlloc LLVMData SizeInfo
  | LLVMOpFree LLVMData SizeInfo Int -- (var, size-of-var, name-of-free)   (name-of-free is only for optimization)
  | LLVMOpUnaryOp UnaryOp LLVMData
  | LLVMOpBinaryOp BinaryOp LLVMData LLVMData
  | LLVMOpSyscall
      Integer -- syscall number
      [LLVMData] -- arguments
  deriving (Show)

type SizeInfo =
  LowType

type SubstLLVM =
  IntMap.IntMap LLVMData

substLLVMData :: SubstLLVM -> LLVMData -> LLVMData
substLLVMData sub llvmData =
  case llvmData of
    LLVMDataLocal x ->
      case IntMap.lookup (asInt x) sub of
        Just d ->
          d
        Nothing ->
          LLVMDataLocal x
    _ ->
      llvmData

substLLVMOp :: SubstLLVM -> LLVMOp -> LLVMOp
substLLVMOp sub llvmOp =
  case llvmOp of
    LLVMOpCall d ds -> do
      let d' = substLLVMData sub d
      let ds' = map (substLLVMData sub) ds
      LLVMOpCall d' ds'
    LLVMOpGetElementPtr (d, t) dts -> do
      let d' = substLLVMData sub d
      let (ds, ts) = unzip dts
      let ds' = map (substLLVMData sub) ds
      LLVMOpGetElementPtr (d', t) (zip ds' ts)
    LLVMOpBitcast d t1 t2 -> do
      let d' = substLLVMData sub d
      LLVMOpBitcast d' t1 t2
    LLVMOpIntToPointer d t1 t2 -> do
      let d' = substLLVMData sub d
      LLVMOpIntToPointer d' t1 t2
    LLVMOpPointerToInt d t1 t2 -> do
      let d' = substLLVMData sub d
      LLVMOpPointerToInt d' t1 t2
    LLVMOpLoad d t -> do
      let d' = substLLVMData sub d
      LLVMOpLoad d' t
    LLVMOpStore t d1 d2 -> do
      let d1' = substLLVMData sub d1
      let d2' = substLLVMData sub d2
      LLVMOpStore t d1' d2'
    LLVMOpAlloc d sizeInfo -> do
      let d' = substLLVMData sub d
      LLVMOpAlloc d' sizeInfo
    LLVMOpFree d sizeInfo i -> do
      let d' = substLLVMData sub d
      LLVMOpFree d' sizeInfo i
    LLVMOpUnaryOp op d -> do
      let d' = substLLVMData sub d
      LLVMOpUnaryOp op d'
    LLVMOpBinaryOp op d1 d2 -> do
      let d1' = substLLVMData sub d1
      let d2' = substLLVMData sub d2
      LLVMOpBinaryOp op d1' d2'
    LLVMOpSyscall i ds -> do
      let ds' = map (substLLVMData sub) ds
      LLVMOpSyscall i ds'
