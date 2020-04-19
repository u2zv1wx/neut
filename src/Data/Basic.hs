module Data.Basic where

import Codec.Binary.UTF8.String
import Data.Binary hiding (encode)
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Text as T
import GHC.Generics hiding (Meta)
import Path
import Path.Internal
import Text.Read hiding (get)

newtype Ident
  = I (T.Text, Int)
  deriving (Eq, Ord, Generic)

instance Binary Ident

asText :: Ident -> T.Text
asText (I (s, _)) = s

asText' :: Ident -> T.Text
asText' (I (s, i)) = s <> "-" <> T.pack (show i)

asText'' :: Ident -> T.Text
asText'' (I (_, i)) = "_" <> T.pack (show i)

asIdent :: T.Text -> Ident
asIdent s = I (s, 0)

asInt :: Ident -> Int
asInt (I (_, i)) = i

instance Show Ident where
  show (I (s, i)) = T.unpack s ++ "-" ++ show i

type Phase = Int

type Line = Int

type Column = Int

type Loc = (Phase, Line, Column)

unwrapPath :: Path a b -> FilePath
unwrapPath (Path path) = path

data Meta
  = Meta
      { metaFileName :: Path Abs File,
        metaLocation :: Loc,
        metaIsReducible :: Bool
      }
  deriving (Generic)

instance Binary Meta where
  put m = do
    put $ unwrapPath $ metaFileName m
    put $ metaLocation m
    put $ metaIsReducible m
  get = do
    path <- get
    loc <- get
    isReducible <- get
    return $
      Meta
        { metaFileName = Path path,
          metaLocation = loc,
          metaIsReducible = isReducible
        }

-- required to derive the eqality on WeakTerm
instance Eq Meta where
  _ == _ = True

instance Show Meta where
  show _ = "_"

instance Ord Meta where
  compare _ _ = EQ

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
      metaIsReducible = metaIsReducible m1 && metaIsReducible m2
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
  Meta {metaFileName = path, metaLocation = (0, l, c), metaIsReducible = True}

type PosInfo = (Path Abs File, Loc)

getPosInfo :: Meta -> PosInfo
getPosInfo m = (metaFileName m, metaLocation m)

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) = toFilePath path ++ ":" ++ show l ++ ":" ++ show c

type IntSize = Int

data FloatSize
  = FloatSize16
  | FloatSize32
  | FloatSize64
  deriving (Eq, Ord, Show, Generic)

instance Binary FloatSize

asFloatSize :: Int -> Maybe FloatSize
asFloatSize 16 = Just FloatSize16
asFloatSize 32 = Just FloatSize32
asFloatSize 64 = Just FloatSize64
asFloatSize _ = Nothing

showFloatSize :: FloatSize -> T.Text
showFloatSize FloatSize16 = "f16"
showFloatSize FloatSize32 = "f32"
showFloatSize FloatSize64 = "f64"

data EnumType
  = EnumTypeLabel T.Text
  | EnumTypeIntS Int -- i{k}
  | EnumTypeIntU Int -- u{k}
  deriving (Show, Eq, Generic)

instance Binary EnumType

data EnumValue
  = EnumValueIntS IntSize Integer
  | EnumValueIntU IntSize Integer
  | EnumValueLabel T.Text
  deriving (Show, Eq, Ord, Generic)

instance Binary EnumValue

data Case
  = CaseValue EnumValue
  | CaseDefault
  deriving (Show, Eq, Ord, Generic)

instance Binary Case

type CasePlus = (Meta, Case)

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

-- これasArrayKindMaybeから実装したほうがよさそう？
asLowTypeMaybe :: T.Text -> Maybe LowType
asLowTypeMaybe s =
  case T.uncons s of
    Just ('i', rest)
      | Just n <- readMaybe $ T.unpack rest,
        0 < n && n <= 64 ->
        Just $ LowTypeIntS n
    Just ('u', rest)
      | Just n <- readMaybe $ T.unpack rest,
        0 < n && n <= 64 ->
        Just $ LowTypeIntU n
    Just ('f', rest)
      | Just n <- readMaybe $ T.unpack rest,
        Just size <- asFloatSize n ->
        Just $ LowTypeFloat size
    _ -> Nothing

sizeAsInt :: FloatSize -> Int
sizeAsInt FloatSize16 = 16
sizeAsInt FloatSize32 = 32
sizeAsInt FloatSize64 = 64

data ArrayKind
  = ArrayKindIntS Int
  | ArrayKindIntU Int
  | ArrayKindFloat FloatSize
  | ArrayKindVoidPtr
  deriving (Show, Eq, Generic)

instance Binary ArrayKind

voidPtr :: LowType
voidPtr = LowTypePtr (LowTypeIntS 8)

arrVoidPtr :: ArrayKind
arrVoidPtr = ArrayKindVoidPtr

asArrayAccessMaybe :: T.Text -> Maybe LowType
asArrayAccessMaybe name
  | Just (typeStr, "array-access") <- breakOnMaybe ":" name =
    asLowTypeMaybe typeStr
  | otherwise = Nothing

lowTypeToArrayKindMaybe :: LowType -> Maybe ArrayKind
lowTypeToArrayKindMaybe (LowTypeIntS i) = Just $ ArrayKindIntS i
lowTypeToArrayKindMaybe (LowTypeIntU i) = Just $ ArrayKindIntU i
lowTypeToArrayKindMaybe (LowTypeFloat size) = Just $ ArrayKindFloat size
lowTypeToArrayKindMaybe _ = Nothing

asArrayKindMaybe :: T.Text -> Maybe ArrayKind
asArrayKindMaybe "" = Nothing
asArrayKindMaybe s
  | 'i' <- T.head s,
    Just n <- readMaybe $ T.unpack $ T.tail s,
    0 < n && n <= 64 =
    Just $ ArrayKindIntS n
asArrayKindMaybe s
  | 'u' <- T.head s,
    Just n <- readMaybe $ T.unpack $ T.tail s,
    0 < n && n <= 64 =
    Just $ ArrayKindIntU n
asArrayKindMaybe s
  | 'f' <- T.head s,
    Just n <- readMaybe $ T.unpack $ T.tail s,
    Just size <- asFloatSize n =
    Just $ ArrayKindFloat size
asArrayKindMaybe _ = Nothing

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
asUnaryOpMaybe name
  | Just (domTypeStr, rest) <- breakOnMaybe ":" name,
    Just (convOpStr, codTypeStr) <- breakOnMaybe ":" rest,
    Just domType <- asLowTypeMaybe domTypeStr,
    Just codType <- asLowTypeMaybe codTypeStr,
    Just op <- asConvOpMaybe domType codType convOpStr =
    Just op
asUnaryOpMaybe _ = Nothing

unaryOpToDomCod :: UnaryOp -> (LowType, LowType)
unaryOpToDomCod (UnaryOpNeg t) = (t, t)
unaryOpToDomCod (UnaryOpTrunc dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpZext dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpSext dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpFpExt dom cod) = (dom, cod)
unaryOpToDomCod (UnaryOpTo dom cod) = (dom, cod)

asConvOpMaybe :: LowType -> LowType -> T.Text -> Maybe UnaryOp
asConvOpMaybe domType codType "trunc" = Just $ UnaryOpTrunc domType codType
asConvOpMaybe domType codType "zext" = Just $ UnaryOpZext domType codType
asConvOpMaybe domType codType "sext" = Just $ UnaryOpSext domType codType
asConvOpMaybe domType codType "ext" = Just $ UnaryOpFpExt domType codType
asConvOpMaybe domType codType "to" = Just $ UnaryOpTo domType codType
asConvOpMaybe _ _ _ = Nothing

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
asBinaryOpMaybe _ = Nothing

binaryOpToDomCod :: BinaryOp -> (LowType, LowType)
binaryOpToDomCod (BinaryOpAdd t) = (t, t)
binaryOpToDomCod (BinaryOpSub t) = (t, t)
binaryOpToDomCod (BinaryOpMul t) = (t, t)
binaryOpToDomCod (BinaryOpDiv t) = (t, t)
binaryOpToDomCod (BinaryOpRem t) = (t, t)
binaryOpToDomCod (BinaryOpEQ t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpNE t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpGT t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpGE t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpLT t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpLE t) = (t, LowTypeIntS 1)
binaryOpToDomCod (BinaryOpShl t) = (t, t)
binaryOpToDomCod (BinaryOpLshr t) = (t, t)
binaryOpToDomCod (BinaryOpAshr t) = (t, t)
binaryOpToDomCod (BinaryOpAnd t) = (t, t)
binaryOpToDomCod (BinaryOpOr t) = (t, t)
binaryOpToDomCod (BinaryOpXor t) = (t, t)

asBinaryOpMaybe' :: T.Text -> Maybe (LowType -> BinaryOp)
asBinaryOpMaybe' "add" = Just BinaryOpAdd
asBinaryOpMaybe' "sub" = Just BinaryOpSub
asBinaryOpMaybe' "mul" = Just BinaryOpMul
asBinaryOpMaybe' "div" = Just BinaryOpDiv
asBinaryOpMaybe' "rem" = Just BinaryOpRem
asBinaryOpMaybe' "eq" = Just BinaryOpEQ
asBinaryOpMaybe' "ne" = Just BinaryOpNE
asBinaryOpMaybe' "gt" = Just BinaryOpGT
asBinaryOpMaybe' "ge" = Just BinaryOpGE
asBinaryOpMaybe' "lt" = Just BinaryOpLT
asBinaryOpMaybe' "<" = Just BinaryOpLT
asBinaryOpMaybe' "le" = Just BinaryOpLE
asBinaryOpMaybe' "shl" = Just BinaryOpShl
asBinaryOpMaybe' "lshr" = Just BinaryOpLshr
asBinaryOpMaybe' "ashr" = Just BinaryOpAshr
asBinaryOpMaybe' "and" = Just BinaryOpAnd
asBinaryOpMaybe' "or" = Just BinaryOpOr
asBinaryOpMaybe' "xor" = Just BinaryOpXor
asBinaryOpMaybe' _ = Nothing

type Target = (OS, Arch)

data OS
  = OSLinux
  | OSDarwin
  deriving (Eq, Show)

showOS :: OS -> T.Text
showOS OSLinux = "linux"
showOS OSDarwin = "darwin"

data Arch
  = Arch64
  deriving (Eq, Show)

showArch :: Arch -> T.Text
showArch Arch64 = "x64"

-- Left name-of-interface-function | Right (name-of-syscall, number-of-syscall)
-- the `Left` here is required since direct use of syscall in macOS is deprecated since 10.12, and thus we need to
-- use corresponding interface functions.
type Syscall = Either T.Text (T.Text, Integer)

linearCheck :: (Eq a, Ord a) => [a] -> Bool
linearCheck = linearCheck' S.empty

linearCheck' :: (Eq a, Ord a) => S.Set a -> [a] -> Bool
linearCheck' _ [] = True
linearCheck' found (x : _)
  | x `S.member` found = False
linearCheck' found (x : xs) = linearCheck' (S.insert x found) xs

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
deleteKeys = foldr IntMap.delete

showInHex :: T.Text -> T.Text
showInHex x = "x" <> foldr (<>) "" (map showInHex' (encode $ T.unpack x))

showInHex' :: Word8 -> T.Text
showInHex' w = do
  let (high, low) = (fromIntegral w :: Int) `divMod` 16
  hex high <> hex low

hex :: Int -> T.Text
hex 0 = "0"
hex 1 = "1"
hex 2 = "2"
hex 3 = "3"
hex 4 = "4"
hex 5 = "5"
hex 6 = "6"
hex 7 = "7"
hex 8 = "8"
hex 9 = "9"
hex 10 = "a"
hex 11 = "b"
hex 12 = "c"
hex 13 = "d"
hex 14 = "e"
hex 15 = "f"
hex _ = " "

fmap2 :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
fmap2 f = fmap (fmap f)

fmap2M :: (Monad m) => (b -> m c) -> Maybe (a, b) -> m (Maybe (a, c))
fmap2M _ Nothing = return Nothing
fmap2M f (Just (x, y)) = do
  y' <- f y
  return $ Just (x, y')
