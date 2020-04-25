module Data.Basic where

import Codec.Binary.UTF8.String
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Word
import GHC.Generics hiding (Meta)
import Path
import Path.Internal
import Text.Read hiding (get)

newtype Ident
  = I (T.Text, Int)
  deriving (Eq, Ord, Generic)

asText :: Ident -> T.Text
asText (I (s, _)) =
  s

asText' :: Ident -> T.Text
asText' (I (s, i)) =
  s <> "-" <> T.pack (show i)

asText'' :: Ident -> T.Text
asText'' (I (_, i)) =
  "_" <> T.pack (show i)

asIdent :: T.Text -> Ident
asIdent s =
  I (s, 0)

asInt :: Ident -> Int
asInt (I (_, i)) =
  i

instance Show Ident where
  show (I (s, i)) =
    T.unpack s ++ "-" ++ show i

{-# INLINE nsSep #-}
nsSep :: T.Text
nsSep =
  "."

{-# INLINE boolTrue #-}
boolTrue :: T.Text
boolTrue =
  "bool" <> nsSep <> "true"

{-# INLINE boolFalse #-}
boolFalse :: T.Text
boolFalse =
  "bool" <> nsSep <> "false"

type Phase =
  Int

type Line =
  Int

type Column =
  Int

type Loc =
  (Phase, Line, Column)

unwrapPath :: Path a b -> FilePath
unwrapPath (Path path) =
  path

data Meta
  = Meta
      { metaFileName :: Path Abs File,
        metaLocation :: Loc,
        metaIsReducible :: Bool,
        metaIsExplicit :: Bool
      }
  deriving (Generic)

-- required to derive the eqality on WeakTerm
instance Eq Meta where
  _ == _ =
    True

instance Show Meta where
  show _ =
    "_"

instance Ord Meta where
  compare _ _ =
    EQ

showMeta :: Meta -> String
showMeta m = do
  let name = metaFileName m
  let (_, l, c) = metaLocation m
  toFilePath name ++ ":" ++ show l ++ ":" ++ show c

showMeta' :: Meta -> String
showMeta' m = do
  let name = metaFileName m
  let (ph, l, c) = metaLocation m
  toFilePath name ++ ":" ++ show ph ++ ":" ++ show l ++ ":" ++ show c

supMeta :: Meta -> Meta -> Meta
supMeta m1 m2 =
  Meta
    { metaFileName = supFileName m1 m2,
      metaLocation = supLocation m1 m2,
      metaIsReducible = metaIsReducible m1 && metaIsReducible m2,
      metaIsExplicit = metaIsExplicit m1 || metaIsExplicit m2
    }

supFileName :: Meta -> Meta -> Path Abs File
supFileName m1 m2 =
  case metaLocation m1 `compare` metaLocation m2 of
    GT -> metaFileName m1
    _ -> metaFileName m2

supLocation :: Meta -> Meta -> Loc
supLocation m1 m2 =
  case metaLocation m1 `compare` metaLocation m2 of
    GT -> metaLocation m1
    _ -> metaLocation m2

newMeta :: Int -> Int -> Path Abs File -> Meta
newMeta l c path =
  Meta
    { metaFileName = path,
      metaLocation = (0, l, c),
      metaIsReducible = True,
      metaIsExplicit = False
    }

type PosInfo =
  (Path Abs File, Loc)

getPosInfo :: Meta -> PosInfo
getPosInfo m =
  (metaFileName m, metaLocation m)

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) =
  toFilePath path ++ ":" ++ show l ++ ":" ++ show c

type IntSize =
  Int

data FloatSize
  = FloatSize16
  | FloatSize32
  | FloatSize64
  deriving (Eq, Ord, Show, Generic)

asFloatSize :: Int -> Maybe FloatSize
asFloatSize size =
  case size of
    16 ->
      Just FloatSize16
    32 ->
      Just FloatSize32
    64 ->
      Just FloatSize64
    _ ->
      Nothing

showIntSize :: IntSize -> T.Text
showIntSize size =
  "i" <> T.pack (show size)

showFloatSize :: FloatSize -> T.Text
showFloatSize size =
  case size of
    FloatSize16 ->
      "f16"
    FloatSize32 ->
      "f32"
    FloatSize64 ->
      "f64"

data EnumCase
  = EnumCaseLabel T.Text
  | EnumCaseDefault
  deriving (Show, Eq, Ord, Generic)

type EnumCasePlus =
  (Meta, EnumCase)

data LowType
  = LowTypeInt IntSize
  | LowTypeBool -- synonym for i1
  | LowTypeFloat FloatSize
  | LowTypeVoid -- to represent the cod of free
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStruct [LowType]
  | LowTypeArray Int LowType -- [n x LOWTYPE]
  | LowTypePtr LowType
  deriving (Eq, Ord, Show)

asLowTypeMaybe :: T.Text -> Maybe LowType
asLowTypeMaybe name = do
  kind <- asArrayKindMaybe name
  return $ arrayKindToLowType kind

sizeAsInt :: FloatSize -> Int
sizeAsInt size =
  case size of
    FloatSize16 ->
      16
    FloatSize32 ->
      32
    FloatSize64 ->
      64

data ArrayKind
  = ArrayKindInt Int
  | ArrayKindFloat FloatSize
  | ArrayKindVoidPtr
  deriving (Show, Eq, Generic)

voidPtr :: LowType
voidPtr =
  LowTypePtr (LowTypeInt 8)

arrVoidPtr :: ArrayKind
arrVoidPtr =
  ArrayKindVoidPtr

asArrayAccessMaybe :: T.Text -> Maybe LowType
asArrayAccessMaybe name
  | Just (typeStr, "array-access") <- breakOnMaybe nsSep name =
    asLowTypeMaybe typeStr
  | otherwise =
    Nothing

lowTypeToArrayKindMaybe :: LowType -> Maybe ArrayKind
lowTypeToArrayKindMaybe lowType =
  case lowType of
    LowTypeInt i ->
      Just $ ArrayKindInt i
    LowTypeFloat size ->
      Just $ ArrayKindFloat size
    _ ->
      Nothing

arrayKindToLowType :: ArrayKind -> LowType
arrayKindToLowType arrayKind =
  case arrayKind of
    ArrayKindInt i ->
      LowTypeInt i
    ArrayKindFloat size ->
      LowTypeFloat size
    ArrayKindVoidPtr ->
      voidPtr

asArrayKindMaybe :: T.Text -> Maybe ArrayKind
asArrayKindMaybe s =
  case T.uncons s of
    Nothing ->
      Nothing
    Just (c, rest) ->
      case c of
        'i'
          | Just n <- readMaybe $ T.unpack rest,
            1 <= n,
            n <= 64 ->
            Just $ ArrayKindInt n
        'f'
          | Just n <- readMaybe $ T.unpack rest,
            Just size <- asFloatSize n ->
            Just $ ArrayKindFloat size
        _ ->
          Nothing

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
    "fptrunc"
      | LowTypeFloat size1 <- domType,
        LowTypeFloat size2 <- codType,
        sizeAsInt size1 > sizeAsInt size2 ->
        Just $ UnaryOpFpTrunc domType codType
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
      (t, LowTypeBool)
    BinaryOpICmpNE t ->
      (t, LowTypeBool)
    BinaryOpICmpUGT t ->
      (t, LowTypeBool)
    BinaryOpICmpUGE t ->
      (t, LowTypeBool)
    BinaryOpICmpULT t ->
      (t, LowTypeBool)
    BinaryOpICmpULE t ->
      (t, LowTypeBool)
    BinaryOpICmpSGT t ->
      (t, LowTypeBool)
    BinaryOpICmpSGE t ->
      (t, LowTypeBool)
    BinaryOpICmpSLT t ->
      (t, LowTypeBool)
    BinaryOpICmpSLE t ->
      (t, LowTypeBool)
    BinaryOpFCmpFALSE t ->
      (t, LowTypeBool)
    BinaryOpFCmpOEQ t ->
      (t, LowTypeBool)
    BinaryOpFCmpOGT t ->
      (t, LowTypeBool)
    BinaryOpFCmpOGE t ->
      (t, LowTypeBool)
    BinaryOpFCmpOLT t ->
      (t, LowTypeBool)
    BinaryOpFCmpOLE t ->
      (t, LowTypeBool)
    BinaryOpFCmpONE t ->
      (t, LowTypeBool)
    BinaryOpFCmpORD t ->
      (t, LowTypeBool)
    BinaryOpFCmpUEQ t ->
      (t, LowTypeBool)
    BinaryOpFCmpUGT t ->
      (t, LowTypeBool)
    BinaryOpFCmpUGE t ->
      (t, LowTypeBool)
    BinaryOpFCmpULT t ->
      (t, LowTypeBool)
    BinaryOpFCmpULE t ->
      (t, LowTypeBool)
    BinaryOpFCmpUNE t ->
      (t, LowTypeBool)
    BinaryOpFCmpUNO t ->
      (t, LowTypeBool)
    BinaryOpFCmpTRUE t ->
      (t, LowTypeBool)

type Target =
  (OS, Arch)

data OS
  = OSLinux
  | OSDarwin
  deriving (Eq, Show)

showOS :: OS -> T.Text
showOS os =
  case os of
    OSLinux ->
      "linux"
    OSDarwin ->
      "darwin"

data Arch
  = Arch64
  deriving (Eq, Show)

showArch :: Arch -> T.Text
showArch Arch64 =
  "x64"

-- Left name-of-interface-function | Right (name-of-syscall, number-of-syscall)
-- the `Left` here is required since direct use of syscall in macOS is deprecated since 10.12, and thus we need to
-- use corresponding interface functions.
type Syscall =
  Either T.Text (T.Text, Integer)

linearCheck :: (Eq a, Ord a) => [a] -> Bool
linearCheck =
  linearCheck' S.empty

linearCheck' :: (Eq a, Ord a) => S.Set a -> [a] -> Bool
linearCheck' found input =
  case input of
    [] ->
      True
    (x : xs)
      | x `S.member` found ->
        False
      | otherwise ->
        linearCheck' (S.insert x found) xs

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

deleteKeys :: IntMap.IntMap a -> [Int] -> IntMap.IntMap a
deleteKeys =
  foldr IntMap.delete

showInHex :: T.Text -> T.Text
showInHex x =
  "x" <> foldr (<>) "" (map showInHex' (encode $ T.unpack x))

showInHex' :: Word8 -> T.Text
showInHex' w = do
  let (high, low) = (fromIntegral w :: Int) `divMod` 16
  hex high <> hex low

hex :: Int -> T.Text
hex i =
  T.singleton $ "0123456789abcdef" !! i

fmap2 :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 f =
  fmap (fmap f)
