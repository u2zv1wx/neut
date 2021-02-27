module Data.Comp where

import Data.EnumCase
import Data.Exploit
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.LowType
import Data.Maybe (fromMaybe)
import Data.Primitive
import Data.Size
import qualified Data.Text as T

data Value
  = ValueConst T.Text
  | ValueUpsilon Ident
  | ValueSigmaIntro ArrayKind [ValuePlus]
  | ValueInt IntSize Integer
  | ValueFloat FloatSize Double
  | ValueEnumIntro T.Text
  | ValueStructIntro [(ValuePlus, ArrayKind)]
  deriving (Show)

data Comp
  = CompPrimitive Primitive
  | CompPiElimDownElim ValuePlus [ValuePlus] -- ((force v) v1 ... vn)
  | CompSigmaElim ArrayKind [Ident] ValuePlus CompPlus
  | CompUpIntro ValuePlus
  | CompUpElim Ident CompPlus CompPlus
  | CompEnumElim ValuePlus [(EnumCase, CompPlus)]
  | CompStructElim [(Ident, ArrayKind)] ValuePlus CompPlus
  deriving (Show)

data Primitive
  = PrimitiveUnaryOp UnaryOp ValuePlus
  | PrimitiveBinaryOp BinaryOp ValuePlus ValuePlus
  | PrimitiveExploit ExploitKind [ValuePlus]
  deriving (Show)

newtype IsFixed
  = IsFixed Bool
  deriving (Show)

data Definition
  = Definition IsFixed [Ident] CompPlus
  deriving (Show)

type ValuePlus =
  (Hint, Value)

type CompPlus =
  (Hint, Comp)

asUpsilon :: ValuePlus -> Maybe Ident
asUpsilon term =
  case term of
    (_, ValueUpsilon x) ->
      Just x
    _ ->
      Nothing

sigmaIntro :: [ValuePlus] -> Value
sigmaIntro =
  ValueSigmaIntro arrVoidPtr

sigmaElim :: [Ident] -> ValuePlus -> CompPlus -> Comp
sigmaElim =
  CompSigmaElim arrVoidPtr

type SubstValuePlus =
  IntMap.IntMap ValuePlus

substValuePlus :: SubstValuePlus -> ValuePlus -> ValuePlus
substValuePlus sub term =
  case term of
    (m, ValueConst x) ->
      (m, ValueConst x)
    (m, ValueUpsilon s) ->
      fromMaybe (m, ValueUpsilon s) (IntMap.lookup (asInt s) sub)
    (m, ValueSigmaIntro mk vs) -> do
      let vs' = map (substValuePlus sub) vs
      (m, ValueSigmaIntro mk vs')
    (m, ValueInt size l) ->
      (m, ValueInt size l)
    (m, ValueFloat size l) ->
      (m, ValueFloat size l)
    (m, ValueEnumIntro l) ->
      (m, ValueEnumIntro l)
    (m, ValueStructIntro dks) -> do
      let (ds, ks) = unzip dks
      let ds' = map (substValuePlus sub) ds
      (m, ValueStructIntro $ zip ds' ks)

substCompPlus :: SubstValuePlus -> CompPlus -> CompPlus
substCompPlus sub term =
  case term of
    (m, CompPrimitive theta) -> do
      let theta' = substPrimitive sub theta
      (m, CompPrimitive theta')
    (m, CompPiElimDownElim v ds) -> do
      let v' = substValuePlus sub v
      let ds' = map (substValuePlus sub) ds
      (m, CompPiElimDownElim v' ds')
    (m, CompSigmaElim mk xs v e) -> do
      let v' = substValuePlus sub v
      let sub' = foldr IntMap.delete sub (map asInt xs)
      let e' = substCompPlus sub' e
      (m, CompSigmaElim mk xs v' e')
    (m, CompUpIntro v) -> do
      let v' = substValuePlus sub v
      (m, CompUpIntro v')
    (m, CompUpElim x e1 e2) -> do
      let e1' = substCompPlus sub e1
      let sub' = IntMap.delete (asInt x) sub
      let e2' = substCompPlus sub' e2
      (m, CompUpElim x e1' e2')
    (m, CompEnumElim v branchList) -> do
      let v' = substValuePlus sub v
      let (cs, es) = unzip branchList
      let es' = map (substCompPlus sub) es
      (m, CompEnumElim v' (zip cs es'))
    (m, CompStructElim xks v e) -> do
      let v' = substValuePlus sub v
      let sub' = foldr IntMap.delete sub (map (asInt . fst) xks)
      let e' = substCompPlus sub' e
      (m, CompStructElim xks v' e')

substPrimitive :: SubstValuePlus -> Primitive -> Primitive
substPrimitive sub c =
  case c of
    PrimitiveUnaryOp a v -> do
      let v' = substValuePlus sub v
      PrimitiveUnaryOp a v'
    PrimitiveBinaryOp a v1 v2 -> do
      let v1' = substValuePlus sub v1
      let v2' = substValuePlus sub v2
      PrimitiveBinaryOp a v1' v2'
    PrimitiveExploit expKind ds -> do
      let ds' = map (substValuePlus sub) ds
      PrimitiveExploit expKind ds'
