module Data.ConstType where

import Control.Monad.State.Lazy
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Log
import Data.LowType
import Data.Primitive
import Data.Size
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

inferKind :: Hint -> ArrayKind -> WithEnv TermPlus
inferKind m arrayKind =
  case arrayKind of
    ArrayKindInt size ->
      return (m, TermConst (showIntSize size))
    ArrayKindFloat size ->
      return (m, TermConst (showFloatSize size))
    _ ->
      raiseCritical m "inferKind for void-pointer"

termSigmaIntro :: Hint -> [IdentPlus] -> WithEnv TermPlus
termSigmaIntro m xts = do
  z <- newNameWith' "internal.sigma-tau-tuple"
  let vz = (m, TermUpsilon z)
  k <- newNameWith'' "sigma"
  let args = map (\(mx, x, _) -> (mx, TermUpsilon x)) xts
  return
    ( m,
      TermPiIntro
        [ (m, z, (m, TermTau)),
          (m, k, (m, TermPi xts vz))
        ]
        (m, TermPiElim (m, TermUpsilon k) args)
    )
