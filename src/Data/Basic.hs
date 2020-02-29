{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveGeneric #-}

module Data.Basic where

import Data.Hashable
import GHC.Generics (Generic)
import Path

import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as S
import qualified Data.Text as T

-- import Data.Bits
import Data.Maybe (fromMaybe)
import Text.Read

newtype Identifier =
  I (T.Text, Int)
  deriving (Generic, Eq, Ord)

instance Hashable Identifier

asText :: Identifier -> T.Text
asText (I (s, _)) = s

asText' :: Identifier -> T.Text
asText' (I (s, i)) = s <> "-" <> T.pack (show i)

asIdent :: T.Text -> Identifier
asIdent s = I (s, 0)

asInt :: Identifier -> Int
asInt (I (_, i)) = i

instance Show Identifier where
  show (I (s, i)) = T.unpack s ++ "-" ++ show i

data Case
  = CaseValue EnumValue
  | CaseDefault
  deriving (Show, Eq, Ord)

-- note that UnivLevel is just a name of the level of a universe (i.e. the integer
-- itself is not the level of the universe)
type UnivLevel = Int

newtype UnivLevelPlus =
  UnivLevelPlus (Meta, UnivLevel)

instance Show UnivLevelPlus where
  show (UnivLevelPlus (_, l)) = "[" ++ show l ++ "]"
  -- show (UnivLevelPlus (m, l)) = "[" ++ show l ++ "]:" ++ showMeta m

instance Eq UnivLevelPlus where
  (UnivLevelPlus (_, l1)) == (UnivLevelPlus (_, l2)) = l1 == l2

type UnivParams = IntMap.IntMap UnivLevel

type Phase = Int

type Line = Int

type Column = Int

type Loc = (Phase, Line, Column)

data Meta =
  Meta
    { metaFileName :: Maybe (Path Abs File)
    , metaLocation :: Maybe Loc
    , metaConstraintLocation :: Maybe Loc
    , metaIsPublic :: Bool
    , metaIsAppropriateAsCompletionCandidate :: Bool
    , metaUnivParams :: UnivParams
    }

-- required to derive the eqality on WeakTerm
instance Eq Meta where
  _ == _ = True

instance Show Meta where
  show _ = "_"

instance Ord Meta where
  compare _ _ = EQ

showMeta :: Meta -> String
showMeta m =
  case (metaFileName m, metaConstraintLocation m) of
    (Just name, Nothing) -> toFilePath name
    (Just name, Just (_, l, c)) ->
      toFilePath name ++ ":" ++ show l ++ ":" ++ show c
    (Nothing, Nothing) -> "_"
    (Nothing, Just (_, l, c)) -> "<unknown-file>:" ++ show l ++ ":" ++ show c

showMeta' :: Meta -> String
showMeta' m =
  case (metaFileName m, metaConstraintLocation m) of
    (Just name, Nothing) -> toFilePath name
    (Just name, Just (ph, l, c)) ->
      toFilePath name ++ ":" ++ show ph ++ ":" ++ show l ++ ":" ++ show c
    (Nothing, Nothing) -> "_"
    (Nothing, Just (ph, l, c)) ->
      "<unknown-file>:" ++ show ph ++ ":" ++ show l ++ ":" ++ show c

supMeta :: Meta -> Meta -> Meta
supMeta m1 m2
  | metaConstraintLocation m1 < metaConstraintLocation m2 =
    m1 {metaConstraintLocation = metaConstraintLocation m2}
  | otherwise = m1

emptyMeta :: Meta
emptyMeta =
  Meta
    { metaLocation = Nothing
    , metaConstraintLocation = Nothing
    , metaFileName = Nothing
    , metaIsPublic = True
    , metaIsAppropriateAsCompletionCandidate = True
    , metaUnivParams = IntMap.empty
    }

type PosInfo = (Path Abs File, Loc)

getPosInfo :: Meta -> Maybe PosInfo
getPosInfo m =
  case (metaFileName m, metaLocation m) of
    (Just name, Just loc) -> return (name, loc)
    _ -> Nothing

showPosInfo :: Path Abs File -> Loc -> String
showPosInfo path (_, l, c) = toFilePath path ++ ":" ++ show l ++ ":" ++ show c

type IntSize = Int

data FloatSize
  = FloatSize16
  | FloatSize32
  | FloatSize64
  deriving (Eq, Show)

asFloatSize :: Int -> Maybe FloatSize
asFloatSize 16 = Just FloatSize16
asFloatSize 32 = Just FloatSize32
asFloatSize 64 = Just FloatSize64
asFloatSize _ = Nothing

data EnumType
  = EnumTypeLabel T.Text
  | EnumTypeIntS Int -- i{k}
  | EnumTypeIntU Int -- u{k}
  | EnumTypeNat Int -- n{k}
  deriving (Show, Eq)

data EnumValue
  = EnumValueIntS IntSize Integer
  | EnumValueIntU IntSize Integer
  | EnumValueNat Int Int
  | EnumValueLabel T.Text
  deriving (Show, Eq, Ord)

data LowType
  = LowTypeIntS IntSize
  | LowTypeIntU IntSize
  | LowTypeFloat FloatSize
  | LowTypeVoidPtr
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStructPtr [LowType]
  | LowTypeArrayPtr Int LowType -- [n x LOWTYPE]*
  | LowTypeIntS64Ptr
  deriving (Eq, Show)

asLowType :: Identifier -> LowType
asLowType (I (n, _)) = fromMaybe (LowTypeIntS 64) (asLowTypeMaybe n)

asLowTypeMaybe :: T.Text -> Maybe LowType
asLowTypeMaybe "" = Nothing
asLowTypeMaybe s
  | 'i' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n <= 64 = Just $ LowTypeIntS n
asLowTypeMaybe s
  | 'u' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n <= 64 = Just $ LowTypeIntU n
asLowTypeMaybe s
  | 'f' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , Just size <- asFloatSize n = Just $ LowTypeFloat size
asLowTypeMaybe _ = Nothing

asIntS :: Integral a => a -> a -> a
asIntS size n = do
  let upperBound = 2 ^ (size - 1)
  let m = 2 * upperBound
  let a = mod n m
  if a >= upperBound
    then a - m
    else a

asIntU :: Integral a => a -> a -> a
asIntU size n = mod n (2 ^ size)

sizeAsInt :: FloatSize -> Int
sizeAsInt FloatSize16 = 16
sizeAsInt FloatSize32 = 32
sizeAsInt FloatSize64 = 64

data ArrayKind
  = ArrayKindIntS Int
  | ArrayKindIntU Int
  | ArrayKindFloat FloatSize
  | ArrayKindVoidPtr
  deriving (Show, Eq)

voidPtr :: LowType
voidPtr = LowTypeVoidPtr

arrVoidPtr :: ArrayKind
arrVoidPtr = ArrayKindVoidPtr

asArrayAccessMaybe :: T.Text -> Maybe LowType
asArrayAccessMaybe name
  | [typeStr, "array-access"] <- wordsBy ':' name = asLowTypeMaybe typeStr
  | otherwise = Nothing

-- asArrayAccessMaybe :: Identifier -> Maybe LowType
-- asArrayAccessMaybe (I (name, _))
--   | ["array-access", typeStr] <- sepAtLast '-' name
--   , Just lowType <- asLowTypeMaybe typeStr = Just lowType
-- asArrayAccessMaybe _ = Nothing
-- sepAtLast :: Char -> T.Text -> [T.Text]
-- sepAtLast c s =
--   case wordsBy c s of
--     [] -> []
--     [s'] -> [s']
--     ss -> [T.intercalate (T.singleton c) (init ss), last ss]
lowTypeToArrayKindMaybe :: LowType -> Maybe ArrayKind
lowTypeToArrayKindMaybe (LowTypeIntS i) = Just $ ArrayKindIntS i
lowTypeToArrayKindMaybe (LowTypeIntU i) = Just $ ArrayKindIntU i
lowTypeToArrayKindMaybe (LowTypeFloat size) = Just $ ArrayKindFloat size
lowTypeToArrayKindMaybe _ = Nothing

asArrayKindMaybe :: T.Text -> Maybe ArrayKind
asArrayKindMaybe "" = Nothing
asArrayKindMaybe s
  | 'i' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n <= 64 = Just $ ArrayKindIntS n
asArrayKindMaybe s
  | 'u' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , 0 < n && n <= 64 = Just $ ArrayKindIntU n
asArrayKindMaybe s
  | 'f' <- T.head s
  , Just n <- readMaybe $ T.unpack $ T.tail s
  , Just size <- asFloatSize n = Just $ ArrayKindFloat size
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
  | [typeStr, "neg"] <- wordsBy '.' name
  , Just lowType <- asLowTypeMaybe typeStr = Just $ UnaryOpNeg lowType
asUnaryOpMaybe name
  | [domTypeStr, convOpStr, codTypeStr] <- wordsBy '.' name
  , Just domType <- asLowTypeMaybe domTypeStr
  , Just codType <- asLowTypeMaybe codTypeStr
  , Just op <- asConvOpMaybe domType codType convOpStr = Just op
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
  | [typeStr, opStr] <- wordsBy '.' name -- e.g. name == "i8.add"
  , Just lowType <- asLowTypeMaybe typeStr
  , Just f <- asBinaryOpMaybe' opStr = Just $ f lowType
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
asBinaryOpMaybe' "le" = Just BinaryOpLE
asBinaryOpMaybe' "shl" = Just BinaryOpShl
asBinaryOpMaybe' "lshr" = Just BinaryOpLshr
asBinaryOpMaybe' "ashr" = Just BinaryOpAshr
asBinaryOpMaybe' "and" = Just BinaryOpAnd
asBinaryOpMaybe' "or" = Just BinaryOpOr
asBinaryOpMaybe' "xor" = Just BinaryOpXor
asBinaryOpMaybe' _ = Nothing

data SysCall
  = SysCallWrite
  | SysCallRead
  | SysCallExit
  | SysCallOpen
  | SysCallClose
  | SysCallFork
  | SysCallSocket
  | SysCallListen
  | SysCallWait4
  | SysCallBind
  | SysCallAccept
  | SysCallConnect
  deriving (Eq, Show)

type Target = (OS, Arch)

data OS
  = OSLinux
  | OSDarwin
  deriving (Eq, Show)

data Arch =
  Arch64
  deriving (Eq, Show)

-- {} linearCheck {}
linearCheck :: (Eq a, Ord a) => [a] -> Bool
linearCheck xs = linearCheck' S.empty xs

linearCheck' :: (Eq a, Ord a) => (S.Set a) -> [a] -> Bool
linearCheck' _ [] = True
linearCheck' found (x:_)
  | x `S.member` found = False
linearCheck' found (x:xs) = linearCheck' (S.insert x found) xs

wordsBy :: Char -> T.Text -> [T.Text]
wordsBy c s =
  case T.dropWhile (== c) s of
    "" -> []
    s' -> do
      let (w, s'') = T.break (== c) s'
      w : wordsBy c s''

splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast [x] = return ([], x)
splitLast (x:xs) = do
  (xs', z) <- splitLast xs
  return (x : xs', z)
-- ushiftR :: Int -> Int -> Int
-- ushiftR n k = fromIntegral (fromIntegral n `shiftR` k :: Word)
-- ushiftR' :: (Integral a) => a -> Int -> a
-- ushiftR' n k = fromIntegral (fromIntegral n `shiftR` k :: Word)
-- assert :: (Monad m) => String -> Bool -> a -> m a
-- assert str False _ = error str
-- assert _ True x = return x
-- `P` is for "Pure"
-- assertP :: String -> a -> Bool -> a
-- assertP str _ False = error str
-- assertP _ x True = x
-- assert-pure-monadic
-- assertPM :: (Monad m) => String -> a -> m Bool -> m a
-- assertPM msg x m = do
--   b <- m
--   assert msg b x
-- assert-unit-monadic
-- assertUM :: (Monad m) => String -> m Bool -> m ()
-- assertUM msg mb = do
--   b <- mb
--   assert msg b ()
-- assert-unit-pure
-- assertUP :: (Monad m) => String -> Bool -> m ()
-- assertUP msg b = assert msg b ()
-- assert-monadic-monadic
-- assertMM :: (Monad m) => String -> m a -> m Bool -> m a
-- assertMM msg mx mb = do
--   b <- mb
--   x <- mx
--   assert msg b x
-- assert-monadic-pure
-- assertMP :: (Monad m) => String -> m a -> Bool -> m a
-- assertMP msg mx b = do
--   x <- mx
--   assert msg b x
-- assertPreUP :: (Monad m) => String -> Bool -> m ()
-- assertPreUP msg b = assertUP (msg ++ ".pre") b
-- assertPreUM :: (Monad m) => String -> m Bool -> m ()
-- assertPreUM msg mb = assertUM (msg ++ ".pre") mb
-- assertPostMM :: (Monad m) => String -> m a -> m Bool -> m a
-- assertPostMM msg mx mb = assertMM (msg ++ ".post") mx mb
-- assertPostMP :: (Monad m) => String -> m a -> Bool -> m a
-- assertPostMP msg mx b = assertMP (msg ++ ".post") mx b
-- assertPostPM :: (Monad m) => String -> a -> m Bool -> m a
-- assertPostPM msg x mb = assertPM (msg ++ ".post") x mb
