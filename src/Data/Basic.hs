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

showFloatSize :: FloatSize -> T.Text
showFloatSize size =
  case size of
    FloatSize16 ->
      "f16"
    FloatSize32 ->
      "f32"
    FloatSize64 ->
      "f64"

data EnumType
  = EnumTypeLabel T.Text
  | EnumTypeIntS Int -- i{k}
  | EnumTypeIntU Int -- u{k}
  deriving (Show, Eq, Generic)

data EnumValue
  = EnumValueIntS IntSize Integer
  | EnumValueIntU IntSize Integer
  | EnumValueLabel T.Text
  deriving (Show, Eq, Ord, Generic)

data Case
  = CaseValue EnumValue
  | CaseDefault
  deriving (Show, Eq, Ord, Generic)

type CasePlus =
  (Meta, Case)

data LowType
  = LowTypeIntS IntSize
  | LowTypeIntU IntSize
  | LowTypeFloat FloatSize
  | LowTypeVoid -- to represent the cod of free
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStruct [LowType]
  | LowTypeArray Int LowType -- [n x LOWTYPE]
  | LowTypePtr LowType
  deriving (Eq, Ord, Show)

asLowTypeMaybe :: T.Text -> Maybe LowType
asLowTypeMaybe name = do
  (kind, _, _) <- asArrayKindMaybe name
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
  = ArrayKindIntS Int
  | ArrayKindIntU Int
  | ArrayKindFloat FloatSize
  | ArrayKindVoidPtr
  deriving (Show, Eq, Generic)

voidPtr :: LowType
voidPtr =
  LowTypePtr (LowTypeIntS 8)

arrVoidPtr :: ArrayKind
arrVoidPtr =
  ArrayKindVoidPtr

asArrayAccessMaybe :: T.Text -> Maybe LowType
asArrayAccessMaybe name
  | Just (typeStr, "array-access") <- breakOnMaybe ":" name =
    asLowTypeMaybe typeStr
  | otherwise =
    Nothing

lowTypeToArrayKindMaybe :: LowType -> Maybe ArrayKind
lowTypeToArrayKindMaybe lowType =
  case lowType of
    LowTypeIntS i ->
      Just $ ArrayKindIntS i
    LowTypeIntU i ->
      Just $ ArrayKindIntU i
    LowTypeFloat size ->
      Just $ ArrayKindFloat size
    _ ->
      Nothing

arrayKindToLowType :: ArrayKind -> LowType
arrayKindToLowType arrayKind =
  case arrayKind of
    ArrayKindIntS i ->
      LowTypeIntS i
    ArrayKindIntU i ->
      LowTypeIntU i
    ArrayKindFloat size ->
      LowTypeFloat size
    ArrayKindVoidPtr ->
      voidPtr

asArrayKindMaybe :: T.Text -> Maybe (ArrayKind, Char, Int)
asArrayKindMaybe s =
  case T.uncons s of
    Nothing ->
      Nothing
    Just (c, rest) ->
      case c of
        'i'
          | Just n <- readMaybe $ T.unpack rest ->
            Just (ArrayKindIntS n, c, n)
        'u'
          | Just n <- readMaybe $ T.unpack rest ->
            Just (ArrayKindIntU n, c, n)
        'f'
          | Just n <- readMaybe $ T.unpack rest,
            Just size <- asFloatSize n ->
            Just (ArrayKindFloat size, c, n)
        _ ->
          Nothing

data UnaryOp
  = UnaryOpNeg LowType -- fneg : X -> X
  | UnaryOpTrunc LowType LowType -- trunc, fptrunc : X -> Y
  | UnaryOpZext LowType LowType -- zext
  | UnaryOpSext LowType LowType -- sext
  | UnaryOpFpExt LowType LowType -- fpext
  | UnaryOpTo LowType LowType -- fp-to-ui, fp-to-si, ui-to-fp, si-to-fp (f32.to.i32, i32.to.f64, etc.)
  deriving (Eq, Show)

asUnaryOpMaybe :: T.Text -> Maybe UnaryOp
asUnaryOpMaybe name
  | Just (typeStr, "neg") <- breakOnMaybe ":" name,
    Just lowType <- asLowTypeMaybe typeStr =
    Just $ UnaryOpNeg lowType
  | Just (domTypeStr, rest) <- breakOnMaybe ":" name,
    Just (convOpStr, codTypeStr) <- breakOnMaybe ":" rest,
    Just domType <- asLowTypeMaybe domTypeStr,
    Just codType <- asLowTypeMaybe codTypeStr,
    Just op <- asConvOpMaybe domType codType convOpStr =
    Just op
  | otherwise =
    Nothing

unaryOpToDomCod :: UnaryOp -> (LowType, LowType)
unaryOpToDomCod unaryOp =
  case unaryOp of
    UnaryOpNeg t ->
      (t, t)
    UnaryOpTrunc dom cod ->
      (dom, cod)
    UnaryOpZext dom cod ->
      (dom, cod)
    UnaryOpSext dom cod ->
      (dom, cod)
    UnaryOpFpExt dom cod ->
      (dom, cod)
    UnaryOpTo dom cod ->
      (dom, cod)

asConvOpMaybe :: LowType -> LowType -> T.Text -> Maybe UnaryOp
asConvOpMaybe domType codType name =
  case name of
    "trunc" ->
      Just $ UnaryOpTrunc domType codType
    "zext" ->
      Just $ UnaryOpZext domType codType
    "sext" ->
      Just $ UnaryOpSext domType codType
    "ext" ->
      Just $ UnaryOpFpExt domType codType
    "to" ->
      Just $ UnaryOpTo domType codType
    _ ->
      Nothing

data BinaryOp
  = BinaryOpAdd LowType -- (X, X) -> X
  | BinaryOpSub LowType -- (X, X) -> X
  | BinaryOpMul LowType -- (X, X) -> X
  | BinaryOpDiv LowType -- (X, X) -> X
  | BinaryOpRem LowType -- (X, X) -> X
  | BinaryOpEQ LowType -- (X, X) -> bool
  | BinaryOpNE LowType -- (X, X) -> bool
  | BinaryOpGT LowType -- (X, X) -> bool
  | BinaryOpGE LowType -- (X, X) -> bool
  | BinaryOpLT LowType -- (X, X) -> bool
  | BinaryOpLE LowType -- (X, X) -> bool
  | BinaryOpShl LowType -- (X, X) -> X
  | BinaryOpLshr LowType -- (X, X) -> X
  | BinaryOpAshr LowType -- (X, X) -> X
  | BinaryOpAnd LowType -- (X, X) -> X
  | BinaryOpOr LowType -- (X, X) -> X
  | BinaryOpXor LowType -- (X, X) -> X
  deriving (Eq, Show)

asBinaryOpMaybe :: T.Text -> Maybe BinaryOp
asBinaryOpMaybe name
  | Just (typeStr, opStr) <- breakOnMaybe ":" name, -- e.g. name == "i8.add"
    Just lowType <- asLowTypeMaybe typeStr,
    Just f <- asBinaryOpMaybe' opStr =
    Just $ f lowType
  | otherwise =
    Nothing

binaryOpToDomCod :: BinaryOp -> (LowType, LowType)
binaryOpToDomCod binaryOp =
  case binaryOp of
    BinaryOpAdd t ->
      (t, t)
    BinaryOpSub t ->
      (t, t)
    BinaryOpMul t ->
      (t, t)
    BinaryOpDiv t ->
      (t, t)
    BinaryOpRem t ->
      (t, t)
    BinaryOpEQ t ->
      (t, LowTypeIntS 1)
    BinaryOpNE t ->
      (t, LowTypeIntS 1)
    BinaryOpGT t ->
      (t, LowTypeIntS 1)
    BinaryOpGE t ->
      (t, LowTypeIntS 1)
    BinaryOpLT t ->
      (t, LowTypeIntS 1)
    BinaryOpLE t ->
      (t, LowTypeIntS 1)
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

asBinaryOpMaybe' :: T.Text -> Maybe (LowType -> BinaryOp)
asBinaryOpMaybe' name =
  case name of
    "add" ->
      Just BinaryOpAdd
    "sub" ->
      Just BinaryOpSub
    "mul" ->
      Just BinaryOpMul
    "div" ->
      Just BinaryOpDiv
    "rem" ->
      Just BinaryOpRem
    "eq" ->
      Just BinaryOpEQ
    "ne" ->
      Just BinaryOpNE
    "gt" ->
      Just BinaryOpGT
    "ge" ->
      Just BinaryOpGE
    "lt" ->
      Just BinaryOpLT
    "<" ->
      Just BinaryOpLT
    "le" ->
      Just BinaryOpLE
    "shl" ->
      Just BinaryOpShl
    "lshr" ->
      Just BinaryOpLshr
    "ashr" ->
      Just BinaryOpAshr
    "and" ->
      Just BinaryOpAnd
    "or" ->
      Just BinaryOpOr
    "xor" ->
      Just BinaryOpXor
    _ ->
      Nothing

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
  case i of
    0 ->
      "0"
    1 ->
      "1"
    2 ->
      "2"
    3 ->
      "3"
    4 ->
      "4"
    5 ->
      "5"
    6 ->
      "6"
    7 ->
      "7"
    8 ->
      "8"
    9 ->
      "9"
    10 ->
      "a"
    11 ->
      "b"
    12 ->
      "c"
    13 ->
      "d"
    14 ->
      "e"
    15 ->
      "f"
    _ ->
      " "

fmap2 :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 f =
  fmap (fmap f)
