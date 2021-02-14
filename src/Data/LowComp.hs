module Data.LowComp where

import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Primitive
import Data.Size
import qualified Data.Text as T

data LowValue
  = LowValueLocal Ident
  | LowValueGlobal T.Text
  | LowValueInt Integer
  | LowValueFloat FloatSize Double
  | LowValueNull
  deriving (Show)

data LowComp
  = LowCompReturn LowValue -- UpIntro
  | LowCompLet Ident LowOp LowComp -- UpElim
  | LowCompCont LowOp LowComp -- LowCompLet that discards the result of LowOp
  | LowCompSwitch (LowValue, LowType) LowComp [(Int, LowComp)] -- EnumElim
  | LowCompCall LowValue [LowValue]
  | LowCompUnreachable -- for empty case analysis
  deriving (Show)

data LowOp
  = LowOpCall LowValue [LowValue]
  | LowOpGetElementPtr
      (LowValue, LowType) -- (base pointer, the type of base pointer)
      [(LowValue, LowType)] -- [(index, the-typee-of-index)]
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
  | LowOpUnaryOp UnaryOp LowValue
  | LowOpBinaryOp BinaryOp LowValue LowValue
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
    LowValueLocal x ->
      case IntMap.lookup (asInt x) sub of
        Just d ->
          d
        Nothing ->
          LowValueLocal x
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
    LowOpUnaryOp op d -> do
      let d' = substLowValue sub d
      LowOpUnaryOp op d'
    LowOpBinaryOp op d1 d2 -> do
      let d1' = substLowValue sub d1
      let d2' = substLowValue sub d2
      LowOpBinaryOp op d1' d2'
    LowOpSyscall i ds -> do
      let ds' = map (substLowValue sub) ds
      LowOpSyscall i ds'
