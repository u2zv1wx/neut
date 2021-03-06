module Data.LowComp where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.LowType
import qualified Data.Text as T

data LowValue
  = LowValueVarLocal Ident
  | LowValueVarGlobal T.Text
  | LowValueInt Integer
  | LowValueFloat FloatSize Double
  | LowValueNull
  deriving (Show)

data LowComp
  = LowCompReturn LowValue -- UpIntro
  | LowCompLet Ident LowOp LowComp -- UpElim
  -- `LowCompCont` is `LowCompLet` that discards the result of LowOp. This `LowCompCont` is required separately
  -- since LLVM doesn't allow us to write something like `%foo = store i32 3, i32* %ptr`.
  | LowCompCont LowOp LowComp
  | LowCompSwitch (LowValue, LowType) LowComp [(Int, LowComp)] -- EnumElim
  | LowCompCall LowValue [LowValue] -- tail call
  | LowCompUnreachable -- for empty case analysis
  deriving (Show)

data LowOp
  = LowOpCall LowValue [LowValue] -- non-tail call
  | LowOpGetElementPtr
      (LowValue, LowType) -- (base pointer, the type of base pointer)
      [(LowValue, LowType)] -- [(index, the-type-of-index)]
  | LowOpBitcast
      LowValue
      LowType -- cast from
      LowType -- cast to
  | LowOpIntToPointer LowValue LowType LowType
  | LowOpPointerToInt LowValue LowType LowType
  | LowOpLoad LowValue LowType
  | LowOpStore LowType LowValue LowValue
  | LowOpAlloc LowValue SizeInfo
  | LowOpFree LowValue SizeInfo Int -- (var, size-of-var, name-of-free)   (name-of-free is only for optimization)
  | LowOpPrimOp PrimOp [LowValue]
  | LowOpSyscall
      Integer -- syscall number
      [LowValue] -- arguments
  deriving (Show)

type SizeInfo =
  LowType

type SubstLowComp =
  IntMap.IntMap LowValue

substLowValue :: SubstLowComp -> LowValue -> LowValue
substLowValue sub llvmValue =
  case llvmValue of
    LowValueVarLocal x ->
      case IntMap.lookup (asInt x) sub of
        Just d ->
          d
        Nothing ->
          LowValueVarLocal x
    _ ->
      llvmValue

substLowOp :: SubstLowComp -> LowOp -> LowOp
substLowOp sub llvmOp =
  case llvmOp of
    LowOpCall d ds -> do
      let d' = substLowValue sub d
      let ds' = map (substLowValue sub) ds
      LowOpCall d' ds'
    LowOpGetElementPtr (d, t) dts -> do
      let d' = substLowValue sub d
      let (ds, ts) = unzip dts
      let ds' = map (substLowValue sub) ds
      LowOpGetElementPtr (d', t) (zip ds' ts)
    LowOpBitcast d t1 t2 -> do
      let d' = substLowValue sub d
      LowOpBitcast d' t1 t2
    LowOpIntToPointer d t1 t2 -> do
      let d' = substLowValue sub d
      LowOpIntToPointer d' t1 t2
    LowOpPointerToInt d t1 t2 -> do
      let d' = substLowValue sub d
      LowOpPointerToInt d' t1 t2
    LowOpLoad d t -> do
      let d' = substLowValue sub d
      LowOpLoad d' t
    LowOpStore t d1 d2 -> do
      let d1' = substLowValue sub d1
      let d2' = substLowValue sub d2
      LowOpStore t d1' d2'
    LowOpAlloc d sizeInfo -> do
      let d' = substLowValue sub d
      LowOpAlloc d' sizeInfo
    LowOpFree d sizeInfo i -> do
      let d' = substLowValue sub d
      LowOpFree d' sizeInfo i
    LowOpPrimOp op ds -> do
      let ds' = map (substLowValue sub) ds
      LowOpPrimOp op ds'
    LowOpSyscall i ds -> do
      let ds' = map (substLowValue sub) ds
      LowOpSyscall i ds'
