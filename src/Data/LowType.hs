module Data.LowType where

import Data.Size
import qualified Data.Text as T
import Text.Read hiding (get)

data LowType
  = LowTypeInt IntSize
  | LowTypeBool -- synonym for i1
  | LowTypeFloat FloatSize
  | LowTypeFunctionPtr [LowType] LowType
  | LowTypeStruct [LowType]
  | LowTypeArray Int LowType -- [n x LOWTYPE]
  | LowTypePtr LowType
  deriving (Eq, Ord, Show)

asLowTypeMaybe :: T.Text -> Maybe LowType
asLowTypeMaybe name
  | Just intSize <- asLowInt name =
    Just $ LowTypeInt intSize
  | Just floatSize <- asLowFloat name =
    Just $ LowTypeFloat floatSize
  | otherwise =
    Nothing

voidPtr :: LowType
voidPtr =
  LowTypePtr (LowTypeInt 8)

asLowInt :: T.Text -> Maybe IntSize
asLowInt s =
  case T.uncons s of
    Nothing ->
      Nothing
    Just (c, rest) ->
      case c of
        'i'
          | Just n <- readMaybe $ T.unpack rest,
            1 <= n,
            n <= 64 ->
            Just n
        _ ->
          Nothing

asLowFloat :: T.Text -> Maybe FloatSize
asLowFloat s =
  case T.uncons s of
    Nothing ->
      Nothing
    Just (c, rest) ->
      case c of
        'f'
          | Just n <- readMaybe $ T.unpack rest,
            Just size <- asFloatSize n ->
            Just size
        _ ->
          Nothing
