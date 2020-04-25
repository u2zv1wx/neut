module Data.Basic where

import Codec.Binary.UTF8.String
import qualified Data.IntMap as IntMap
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Word
import GHC.Generics hiding (Meta)
import Path
import Path.Internal

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

sizeAsInt :: FloatSize -> Int
sizeAsInt size =
  case size of
    FloatSize16 ->
      16
    FloatSize32 ->
      32
    FloatSize64 ->
      64

data EnumCase
  = EnumCaseLabel T.Text
  | EnumCaseDefault
  deriving (Show, Eq, Ord, Generic)

type EnumCasePlus =
  (Meta, EnumCase)

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
