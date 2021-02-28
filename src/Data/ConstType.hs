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
  | Just op <- asUnaryOpMaybe x =
    unaryOpToType m op
  | Just op <- asBinaryOpMaybe x =
    binaryOpToType m op
  | otherwise = do
    ctenv <- gets constTypeEnv
    case Map.lookup x ctenv of
      Just t -> return t
      Nothing ->
        raiseCritical m $
          "the constant `" <> x <> "` is not found in the type environment."

unaryOpToType :: Hint -> UnaryOp -> WithEnv TermPlus
unaryOpToType m op = do
  let (dom, cod) = unaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x <- newNameWith'' "_"
  let xts = [(m, x, dom')]
  return (m, TermPi xts cod')

binaryOpToType :: Hint -> BinaryOp -> WithEnv TermPlus
binaryOpToType m op = do
  let (dom, cod) = binaryOpToDomCod op
  dom' <- lowTypeToType m dom
  cod' <- lowTypeToType m cod
  x1 <- newNameWith'' "_"
  x2 <- newNameWith'' "_"
  let xts = [(m, x1, dom'), (m, x2, dom')]
  return (m, TermPi xts cod')
