module Data.LowType where

import Data.Size
import qualified Data.Text as T
import Text.Read hiding (get)

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

data ArrayKind
  = ArrayKindInt Int
  | ArrayKindFloat FloatSize
  | ArrayKindVoidPtr
  deriving (Show, Eq)

voidPtr :: LowType
voidPtr =
  LowTypePtr (LowTypeInt 8)

arrVoidPtr :: ArrayKind
arrVoidPtr =
  ArrayKindVoidPtr

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
