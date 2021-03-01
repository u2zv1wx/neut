module Data.ConstType where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Log
import Data.LowType
import Data.Term
import qualified Data.Text as T

lookupConstTypeEnv :: Hint -> T.Text -> WithEnv TermPlus
lookupConstTypeEnv m x
  | Just _ <- asLowTypeMaybe x =
    return (m, TermTau)
  | Just op <- asPrimOp x =
    primOpToType m op
  | otherwise = do
    ctenv <- gets constTypeEnv
    case Map.lookup x ctenv of
      Just t ->
        return t
      Nothing ->
        raiseCritical m $
          "the constant `" <> x <> "` is not found in the type environment."

primOpToType :: Hint -> PrimOp -> WithEnv TermPlus
primOpToType m (PrimOp _ domList cod) = do
  domList' <- mapM (lowTypeToType m) domList
  cod' <- lowTypeToType m cod
  xs <- mapM (const (newNameWith'' "_")) domList'
  let xts = zipWith (\x t -> (m, x, t)) xs domList'
  return (m, TermPi xts cod')
