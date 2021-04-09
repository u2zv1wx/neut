module Data.Comp where

import Data.Basic
import qualified Data.IntMap as IntMap
import Data.LowType
import qualified Data.Set as S
import qualified Data.Text as T

data Value
  = ValueVarLocal Ident
  | ValueVarGlobal T.Text
  | ValueSigmaIntro [ValuePlus]
  | ValueInt IntSize Integer
  | ValueFloat FloatSize Double
  | ValueEnumIntro T.Text
  deriving (Show)

data Comp
  = CompPiElimDownElim ValuePlus [ValuePlus] -- ((force v) v1 ... vn)
  | CompSigmaElim Bool [Ident] ValuePlus CompPlus
  | CompUpIntro ValuePlus
  | CompUpElim Ident CompPlus CompPlus
  | CompEnumElim ValuePlus [(EnumCase, CompPlus)]
  | CompPrimitive Primitive
  deriving (Show)

data Primitive
  = PrimitivePrimOp PrimOp [ValuePlus]
  | PrimitiveDerangement Derangement [ValuePlus]
  deriving (Show)

type ValuePlus =
  (Hint, Value)

type CompPlus =
  (Hint, Comp)

type SubstValuePlus =
  IntMap.IntMap ValuePlus

varValue :: ValuePlus -> S.Set Ident
varValue v =
  case v of
    (_, ValueVarLocal x) ->
      S.singleton x
    (_, ValueSigmaIntro vs) ->
      S.unions $ map varValue vs
    _ ->
      S.empty

varComp :: CompPlus -> S.Set Ident
varComp c =
  case c of
    (_, CompPiElimDownElim v vs) ->
      S.unions $ map varValue (v : vs)
    (_, CompSigmaElim _ xs v e) -> do
      let s1 = varValue v
      let s2 = S.filter (`notElem` xs) $ varComp e
      S.union s1 s2
    (_, CompUpIntro v) ->
      varValue v
    (_, CompUpElim x e1 e2) -> do
      let s1 = varComp e1
      let s2 = S.filter (/= x) $ varComp e2
      S.union s1 s2
    (_, CompEnumElim v caseList) -> do
      let s1 = varValue v
      let (_, es) = unzip caseList
      let s2 = S.unions (map varComp es)
      S.union s1 s2
    (_, CompPrimitive prim) ->
      case prim of
        PrimitivePrimOp _ vs ->
          S.unions $ map varValue vs
        PrimitiveDerangement _ vs ->
          S.unions $ map varValue vs
