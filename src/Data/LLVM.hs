module Data.LLVM where

import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Primitive
import Data.Size
import qualified Data.Text as T

data LLVMValue
  = LLVMValueLocal Ident
  | LLVMValueGlobal T.Text
  | LLVMValueInt Integer
  | LLVMValueFloat FloatSize Double
  | LLVMValueNull
  deriving (Show)

data LLVM
  = LLVMReturn LLVMValue -- UpIntro
  | LLVMLet Ident LLVMOp LLVM -- UpElim
  | LLVMCont LLVMOp LLVM -- LLVMLet that discards the result of LLVMOp
  | LLVMSwitch (LLVMValue, LowType) LLVM [(Int, LLVM)] -- EnumElim
  | LLVMCall LLVMValue [LLVMValue]
  | LLVMUnreachable -- for empty case analysis
  deriving (Show)

data LLVMOp
  = LLVMOpCall LLVMValue [LLVMValue]
  | LLVMOpGetElementPtr
      (LLVMValue, LowType) -- (base pointer, the type of base pointer)
      [(LLVMValue, LowType)] -- [(index, the-typee-of-index)]
  | LLVMOpBitcast
      LLVMValue
      LowType -- cast from
      LowType -- cast to
  | LLVMOpIntToPointer LLVMValue LowType LowType
  | LLVMOpPointerToInt LLVMValue LowType LowType
  | LLVMOpLoad LLVMValue LowType
  | LLVMOpStore LowType LLVMValue LLVMValue
  | LLVMOpAlloc LLVMValue SizeInfo
  | LLVMOpFree LLVMValue SizeInfo Int -- (var, size-of-var, name-of-free)   (name-of-free is only for optimization)
  | LLVMOpUnaryOp UnaryOp LLVMValue
  | LLVMOpBinaryOp BinaryOp LLVMValue LLVMValue
  | LLVMOpSyscall
      Integer -- syscall number
      [LLVMValue] -- arguments
  deriving (Show)

type SizeInfo =
  LowType

type SubstLLVM =
  IntMap.IntMap LLVMValue

substLLVMValue :: SubstLLVM -> LLVMValue -> LLVMValue
substLLVMValue sub llvmValue =
  case llvmValue of
    LLVMValueLocal x ->
      case IntMap.lookup (asInt x) sub of
        Just d ->
          d
        Nothing ->
          LLVMValueLocal x
    _ ->
      llvmValue

substLLVMOp :: SubstLLVM -> LLVMOp -> LLVMOp
substLLVMOp sub llvmOp =
  case llvmOp of
    LLVMOpCall d ds -> do
      let d' = substLLVMValue sub d
      let ds' = map (substLLVMValue sub) ds
      LLVMOpCall d' ds'
    LLVMOpGetElementPtr (d, t) dts -> do
      let d' = substLLVMValue sub d
      let (ds, ts) = unzip dts
      let ds' = map (substLLVMValue sub) ds
      LLVMOpGetElementPtr (d', t) (zip ds' ts)
    LLVMOpBitcast d t1 t2 -> do
      let d' = substLLVMValue sub d
      LLVMOpBitcast d' t1 t2
    LLVMOpIntToPointer d t1 t2 -> do
      let d' = substLLVMValue sub d
      LLVMOpIntToPointer d' t1 t2
    LLVMOpPointerToInt d t1 t2 -> do
      let d' = substLLVMValue sub d
      LLVMOpPointerToInt d' t1 t2
    LLVMOpLoad d t -> do
      let d' = substLLVMValue sub d
      LLVMOpLoad d' t
    LLVMOpStore t d1 d2 -> do
      let d1' = substLLVMValue sub d1
      let d2' = substLLVMValue sub d2
      LLVMOpStore t d1' d2'
    LLVMOpAlloc d sizeInfo -> do
      let d' = substLLVMValue sub d
      LLVMOpAlloc d' sizeInfo
    LLVMOpFree d sizeInfo i -> do
      let d' = substLLVMValue sub d
      LLVMOpFree d' sizeInfo i
    LLVMOpUnaryOp op d -> do
      let d' = substLLVMValue sub d
      LLVMOpUnaryOp op d'
    LLVMOpBinaryOp op d1 d2 -> do
      let d1' = substLLVMValue sub d1
      let d2' = substLLVMValue sub d2
      LLVMOpBinaryOp op d1' d2'
    LLVMOpSyscall i ds -> do
      let ds' = map (substLLVMValue sub) ds
      LLVMOpSyscall i ds'
