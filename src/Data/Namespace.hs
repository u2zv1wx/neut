module Data.Namespace where

import qualified Data.Text as T

nsSepChar :: Char
nsSepChar =
  '.'

{-# INLINE nsSep #-}
nsSep :: T.Text
nsSep =
  T.singleton nsSepChar

{-# INLINE nsOS #-}
nsOS :: T.Text
nsOS =
  "os" <> nsSep

{-# INLINE nsUnsafe #-}
nsUnsafe :: T.Text
nsUnsafe =
  "unsafe" <> nsSep
