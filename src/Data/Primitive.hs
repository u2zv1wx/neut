module Data.Primitive where

import Data.LowType
import Data.Size
import qualified Data.Text as T

data UnaryOp
  = UnaryOpFNeg LowType
  | UnaryOpTrunc LowType LowType
  | UnaryOpZext LowType LowType
  | UnaryOpSext LowType LowType
  | UnaryOpFpTrunc LowType LowType
  | UnaryOpFpExt LowType LowType
  | UnaryOpFU LowType LowType
  | UnaryOpFS LowType LowType
  | UnaryOpUF LowType LowType
  | UnaryOpSF LowType LowType
  deriving (Eq, Show)

-- fneg-f16, uitofp-u32-f64, etc.
-- <OP_NAME_IN_LLVM>-<TYPE-1>-(...)-<TYPE-N>
asUnaryOpMaybe :: T.Text -> Maybe UnaryOp
asUnaryOpMaybe name
  | Just ("fneg", typeStr) <- breakOnMaybe "-" name,
    Just lowType@(LowTypeFloat _) <- asLowTypeMaybe typeStr =
    Just $ UnaryOpFNeg lowType
  | Just (convOpStr, rest) <- breakOnMaybe "-" name,
    Just (domTypeStr, codTypeStr) <- breakOnMaybe "-" rest,
    Just domType <- asLowTypeMaybe domTypeStr,
    Just codType <- asLowTypeMaybe codTypeStr,
    Just op <- asConvOpMaybe domType codType convOpStr =
    Just op
  | otherwise =
    Nothing

unaryOpToDomCod :: UnaryOp -> (LowType, LowType)
unaryOpToDomCod unaryOp =
  case unaryOp of
    UnaryOpFNeg t ->
      (t, t)
    UnaryOpTrunc dom cod ->
      (dom, cod)
    UnaryOpZext dom cod ->
      (dom, cod)
    UnaryOpSext dom cod ->
      (dom, cod)
    UnaryOpFpTrunc dom cod ->
      (dom, cod)
    UnaryOpFpExt dom cod ->
      (dom, cod)
    UnaryOpFU dom cod ->
      (dom, cod)
    UnaryOpFS dom cod ->
      (dom, cod)
    UnaryOpUF dom cod ->
      (dom, cod)
    UnaryOpSF dom cod ->
      (dom, cod)

asConvOpMaybe :: LowType -> LowType -> T.Text -> Maybe UnaryOp
asConvOpMaybe domType codType name =
  case name of
    "trunc"
      | LowTypeInt i1 <- domType,
        LowTypeInt i2 <- codType,
        i1 > i2 ->
        Just $ UnaryOpTrunc domType codType
    "zext"
      | LowTypeInt i1 <- domType,
        LowTypeInt i2 <- codType,
        i1 < i2 ->
        Just $ UnaryOpZext domType codType
    "sext"
      | LowTypeInt i1 <- domType,
        LowTypeInt i2 <- codType,
        i1 < i2 ->
        Just $ UnaryOpSext domType codType
    "fptrunc"
      | LowTypeFloat size1 <- domType,
        LowTypeFloat size2 <- codType,
        sizeAsInt size1 > sizeAsInt size2 ->
        Just $ UnaryOpFpTrunc domType codType
    "fpext"
      | LowTypeFloat size1 <- domType,
        LowTypeFloat size2 <- codType,
        sizeAsInt size1 < sizeAsInt size2 ->
        Just $ UnaryOpFpExt domType codType
    "fptoui"
      | LowTypeFloat _ <- domType,
        LowTypeInt _ <- codType ->
        Just $ UnaryOpFU domType codType
    "fptosi"
      | LowTypeFloat _ <- domType,
        LowTypeInt _ <- codType ->
        Just $ UnaryOpFS domType codType
    "uitofp"
      | LowTypeInt _ <- domType,
        LowTypeFloat _ <- codType ->
        Just $ UnaryOpUF domType codType
    "sitofp"
      | LowTypeInt _ <- domType,
        LowTypeFloat _ <- codType ->
        Just $ UnaryOpSF domType codType
    _ ->
      Nothing

data BinaryOp
  = BinaryOpAdd LowType -- (X, X) -> X
  | BinaryOpFAdd LowType -- (X, X) -> X
  | BinaryOpSub LowType -- (X, X) -> X
  | BinaryOpFSub LowType -- (X, X) -> X
  | BinaryOpMul LowType -- (X, X) -> X
  | BinaryOpFMul LowType -- (X, X) -> X
  | BinaryOpUDiv LowType -- (X, X) -> X
  | BinaryOpSDiv LowType -- (X, X) -> X
  | BinaryOpFDiv LowType -- (X, X) -> X
  | BinaryOpURem LowType -- (X, X) -> X
  | BinaryOpSRem LowType -- (X, X) -> X
  | BinaryOpFRem LowType
  | BinaryOpShl LowType -- (X, X) -> X
  | BinaryOpLshr LowType -- (X, X) -> X
  | BinaryOpAshr LowType -- (X, X) -> X
  | BinaryOpAnd LowType -- (X, X) -> X
  | BinaryOpOr LowType -- (X, X) -> X
  | BinaryOpXor LowType -- (X, X) -> X
  | BinaryOpICmpEQ LowType -- (X, X) -> bool
  | BinaryOpICmpNE LowType -- (X, X) -> bool
  | BinaryOpICmpUGT LowType -- (X, X) -> bool
  | BinaryOpICmpUGE LowType -- (X, X) -> bool
  | BinaryOpICmpULT LowType -- (X, X) -> bool
  | BinaryOpICmpULE LowType -- (X, X) -> bool
  | BinaryOpICmpSGT LowType -- (X, X) -> bool
  | BinaryOpICmpSGE LowType -- (X, X) -> bool
  | BinaryOpICmpSLT LowType -- (X, X) -> bool
  | BinaryOpICmpSLE LowType -- (X, X) -> bool
  | BinaryOpFCmpFALSE LowType -- (X, X) -> bool
  | BinaryOpFCmpOEQ LowType -- (X, X) -> bool
  | BinaryOpFCmpOGT LowType -- (X, X) -> bool
  | BinaryOpFCmpOGE LowType -- (X, X) -> bool
  | BinaryOpFCmpOLT LowType -- (X, X) -> bool
  | BinaryOpFCmpOLE LowType -- (X, X) -> bool
  | BinaryOpFCmpONE LowType -- (X, X) -> bool
  | BinaryOpFCmpORD LowType -- (X, X) -> bool
  | BinaryOpFCmpUEQ LowType -- (X, X) -> bool
  | BinaryOpFCmpUGT LowType -- (X, X) -> bool
  | BinaryOpFCmpUGE LowType -- (X, X) -> bool
  | BinaryOpFCmpULT LowType -- (X, X) -> bool
  | BinaryOpFCmpULE LowType -- (X, X) -> bool
  | BinaryOpFCmpUNE LowType -- (X, X) -> bool
  | BinaryOpFCmpUNO LowType -- (X, X) -> bool
  | BinaryOpFCmpTRUE LowType -- (X, X) -> bool
  deriving (Eq, Show)

-- add-i8, lt-u32, etc.
asBinaryOpMaybe :: T.Text -> Maybe BinaryOp
asBinaryOpMaybe name
  | Just (opStr, rest) <- breakOnMaybe "-" name =
    case opStr of
      "icmp"
        | Just (condStr, typeStr) <- breakOnMaybe "-" rest,
          Just lowType@(LowTypeInt _) <- asLowTypeMaybe typeStr,
          Just f <- asICmpMaybe condStr ->
          Just $ f lowType
      "fcmp"
        | Just (condStr, typeStr) <- breakOnMaybe "-" rest,
          Just lowType@(LowTypeFloat _) <- asLowTypeMaybe typeStr,
          Just f <- asFCmpMaybe condStr ->
          Just $ f lowType
      _
        | Just lowType <- asLowTypeMaybe rest,
          Just f <- asBinaryOpMaybe' opStr lowType ->
          Just $ f lowType
      _ ->
        Nothing
  | otherwise =
    Nothing

asBinaryOpMaybe' :: T.Text -> LowType -> Maybe (LowType -> BinaryOp)
asBinaryOpMaybe' name lowType =
  case name of
    "add"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpAdd
    "fadd"
      | LowTypeFloat _ <- lowType ->
        Just BinaryOpFAdd
    "sub"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpSub
    "fsub"
      | LowTypeFloat _ <- lowType ->
        Just BinaryOpFSub
    "mul"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpMul
    "fmul"
      | LowTypeFloat _ <- lowType ->
        Just BinaryOpFMul
    "udiv"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpUDiv
    "sdiv"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpSDiv
    "fdiv"
      | LowTypeFloat _ <- lowType ->
        Just BinaryOpFDiv
    "urem"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpURem
    "srem"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpSRem
    "frem"
      | LowTypeFloat _ <- lowType ->
        Just BinaryOpFRem
    "shl"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpShl
    "lshr"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpLshr
    "ashr"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpAshr
    "and"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpAnd
    "or"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpOr
    "xor"
      | LowTypeInt _ <- lowType ->
        Just BinaryOpXor
    _ ->
      Nothing

asICmpMaybe :: T.Text -> Maybe (LowType -> BinaryOp)
asICmpMaybe name =
  case name of
    "eq" ->
      Just BinaryOpICmpEQ
    "ne" ->
      Just BinaryOpICmpNE
    "ugt" ->
      Just BinaryOpICmpUGT
    "uge" ->
      Just BinaryOpICmpUGE
    "ult" ->
      Just BinaryOpICmpULT
    "ule" ->
      Just BinaryOpICmpULE
    "sgt" ->
      Just BinaryOpICmpSGT
    "sge" ->
      Just BinaryOpICmpSGE
    "slt" ->
      Just BinaryOpICmpSLT
    "sle" ->
      Just BinaryOpICmpSLE
    _ ->
      Nothing

asFCmpMaybe :: T.Text -> Maybe (LowType -> BinaryOp)
asFCmpMaybe name =
  case name of
    "false" ->
      Just BinaryOpFCmpFALSE
    "oeq" ->
      Just BinaryOpFCmpOEQ
    "ogt" ->
      Just BinaryOpFCmpOGT
    "oge" ->
      Just BinaryOpFCmpOGE
    "olt" ->
      Just BinaryOpFCmpOLT
    "ole" ->
      Just BinaryOpFCmpOLE
    "one" ->
      Just BinaryOpFCmpONE
    "ord" ->
      Just BinaryOpFCmpORD
    "ueq" ->
      Just BinaryOpFCmpUEQ
    "ugt" ->
      Just BinaryOpFCmpUGT
    "uge" ->
      Just BinaryOpFCmpUGE
    "ult" ->
      Just BinaryOpFCmpULT
    "ule" ->
      Just BinaryOpFCmpULE
    "une" ->
      Just BinaryOpFCmpUNE
    "uno" ->
      Just BinaryOpFCmpUNO
    "true" ->
      Just BinaryOpFCmpTRUE
    _ ->
      Nothing

binaryOpToDomCod :: BinaryOp -> (LowType, LowType)
binaryOpToDomCod binaryOp =
  case binaryOp of
    BinaryOpAdd t ->
      (t, t)
    BinaryOpFAdd t ->
      (t, t)
    BinaryOpSub t ->
      (t, t)
    BinaryOpFSub t ->
      (t, t)
    BinaryOpMul t ->
      (t, t)
    BinaryOpFMul t ->
      (t, t)
    BinaryOpUDiv t ->
      (t, t)
    BinaryOpSDiv t ->
      (t, t)
    BinaryOpFDiv t ->
      (t, t)
    BinaryOpURem t ->
      (t, t)
    BinaryOpSRem t ->
      (t, t)
    BinaryOpFRem t ->
      (t, t)
    BinaryOpShl t ->
      (t, t)
    BinaryOpLshr t ->
      (t, t)
    BinaryOpAshr t ->
      (t, t)
    BinaryOpAnd t ->
      (t, t)
    BinaryOpOr t ->
      (t, t)
    BinaryOpXor t ->
      (t, t)
    BinaryOpICmpEQ t ->
      (t, LowTypeInt 1)
    BinaryOpICmpNE t ->
      (t, LowTypeInt 1)
    BinaryOpICmpUGT t ->
      (t, LowTypeInt 1)
    BinaryOpICmpUGE t ->
      (t, LowTypeInt 1)
    BinaryOpICmpULT t ->
      (t, LowTypeInt 1)
    BinaryOpICmpULE t ->
      (t, LowTypeInt 1)
    BinaryOpICmpSGT t ->
      (t, LowTypeInt 1)
    BinaryOpICmpSGE t ->
      (t, LowTypeInt 1)
    BinaryOpICmpSLT t ->
      (t, LowTypeInt 1)
    BinaryOpICmpSLE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpFALSE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpOEQ t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpOGT t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpOGE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpOLT t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpOLE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpONE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpORD t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpUEQ t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpUGT t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpUGE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpULT t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpULE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpUNE t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpUNO t ->
      (t, LowTypeInt 1)
    BinaryOpFCmpTRUE t ->
      (t, LowTypeInt 1)

{-# INLINE breakOnMaybe #-}
breakOnMaybe :: T.Text -> T.Text -> Maybe (T.Text, T.Text)
breakOnMaybe needle text =
  if T.null text
    then Nothing
    else do
      let (h, t) = T.breakOn needle text
      if T.null t
        then Nothing
        else return (h, T.tail t)
