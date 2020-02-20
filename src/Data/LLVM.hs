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
  = AllocSizeExact Int
  | AllocSizePtrList Int
  deriving (Show)

type SubstLLVM = [(Identifier, LLVMData)]

substLLVMData :: SubstLLVM -> LLVMData -> LLVMData
substLLVMData sub (LLVMDataLocal x) =
  case lookup x sub of
    Just d -> d
    Nothing -> LLVMDataLocal x
substLLVMData _ d = d

substLLVM :: SubstLLVM -> LLVM -> LLVM
substLLVM sub (LLVMReturn d) = LLVMReturn $ substLLVMData sub d
substLLVM sub (LLVMLet x op cont) = do
  let op' = substLLVMOp sub op
  let sub' = filter (\(y, _) -> y /= x) sub
  let cont' = substLLVM sub' cont
  LLVMLet x op' cont'
substLLVM sub (LLVMCont op cont) = do
  let op' = substLLVMOp sub op
  let cont' = substLLVM sub cont
  LLVMCont op' cont'
substLLVM sub (LLVMSwitch (d, t) defaultBranch les) = do
  let (ls, es) = unzip les
  let d' = substLLVMData sub d
  let defaultBranch' = substLLVM sub defaultBranch
  let es' = map (substLLVM sub) es
  LLVMSwitch (d', t) defaultBranch' (zip ls es')
substLLVM sub (LLVMCall d ds) = do
  let d' = substLLVMData sub d
  let ds' = map (substLLVMData sub) ds
  LLVMCall d' ds'
substLLVM _ LLVMUnreachable = LLVMUnreachable

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
substLLVMOp sub (LLVMOpAlloc d) = do
  let d' = substLLVMData sub d
  LLVMOpAlloc d'
substLLVMOp sub (LLVMOpFree d) = do
  let d' = substLLVMData sub d
  LLVMOpFree d'
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
