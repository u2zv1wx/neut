module Reduce.Comp
  ( reduceCompPlus,
    substCompPlus,
  )
where

import Control.Monad.State.Lazy
import Data.Basic hiding (asIdent)
import Data.Comp
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap

type NameEnv = IntMap.IntMap Ident

reduceCompPlus :: CompPlus -> WithEnv CompPlus
reduceCompPlus term =
  case term of
    (m, CompPrimitive c) ->
      return (m, CompPrimitive c)
    (m, CompPiElimDownElim v ds) -> do
      cenv <- gets codeEnv
      case v of
        (_, ValueVarGlobal x)
          | Just (Definition isReducible xs body) <- Map.lookup x cenv,
            isReducible,
            length xs == length ds -> do
            let sub = IntMap.fromList (zip (map asInt xs) ds)
            substCompPlus sub IntMap.empty body >>= reduceCompPlus
        _ ->
          return (m, CompPiElimDownElim v ds)
    (m, CompSigmaElim isNoetic xs v e) ->
      case v of
        (_, ValueSigmaIntro ds)
          | length ds == length xs -> do
            let sub = IntMap.fromList (zip (map asInt xs) ds)
            substCompPlus sub IntMap.empty e >>= reduceCompPlus
        _ -> do
          e' <- reduceCompPlus e
          case e' of
            (mUp, CompUpIntro (_, ValueSigmaIntro ds))
              | Just ys <- mapM asIdent ds,
                xs == ys ->
                return (mUp, CompUpIntro v) -- eta-reduce
            _ ->
              case xs of
                [] ->
                  return e'
                _ ->
                  return (m, CompSigmaElim isNoetic xs v e')
    (m, CompUpIntro v) ->
      return (m, CompUpIntro v)
    (m, CompUpElim x e1 e2) -> do
      e1' <- reduceCompPlus e1
      case e1' of
        (_, CompUpIntro d) -> do
          let sub = IntMap.fromList [(asInt x, d)]
          substCompPlus sub IntMap.empty e2 >>= reduceCompPlus
        (my, CompUpElim y ey1 ey2) ->
          reduceCompPlus (my, CompUpElim y ey1 (m, CompUpElim x ey2 e2)) -- commutative conversion
        (my, CompSigmaElim b yts vy ey) ->
          reduceCompPlus (my, CompSigmaElim b yts vy (m, CompUpElim x ey e2)) -- commutative conversion
        _ -> do
          e2' <- reduceCompPlus e2
          case e2' of
            (_, CompUpIntro (_, ValueVarLocal y))
              | x == y ->
                return e1' -- eta-reduce
            _ ->
              return (m, CompUpElim x e1' e2')
    (m, CompEnumElim v les) ->
      case v of
        (_, ValueEnumIntro l)
          | Just body <- lookup (EnumCaseLabel l) les ->
            reduceCompPlus body
          | Just body <- lookup EnumCaseDefault les ->
            reduceCompPlus body
        _ -> do
          let (ls, es) = unzip les
          es' <- mapM reduceCompPlus es
          return (m, CompEnumElim v (zip ls es'))

substValuePlus :: SubstValuePlus -> NameEnv -> ValuePlus -> ValuePlus
substValuePlus sub nenv term =
  case term of
    (m, ValueVarLocal x)
      | Just x' <- IntMap.lookup (asInt x) nenv ->
        (m, ValueVarLocal x')
      | Just e <- IntMap.lookup (asInt x) sub ->
        e
      | otherwise ->
        (m, ValueVarLocal x)
    (m, ValueSigmaIntro vs) -> do
      let vs' = map (substValuePlus sub nenv) vs
      (m, ValueSigmaIntro vs')
    _ ->
      term

substCompPlus :: SubstValuePlus -> NameEnv -> CompPlus -> WithEnv CompPlus
substCompPlus sub nenv term =
  case term of
    (m, CompPrimitive theta) -> do
      let theta' = substPrimitive sub nenv theta
      return (m, CompPrimitive theta')
    (m, CompPiElimDownElim v ds) -> do
      let v' = substValuePlus sub nenv v
      let ds' = map (substValuePlus sub nenv) ds
      return (m, CompPiElimDownElim v' ds')
    (m, CompSigmaElim b xs v e) -> do
      let v' = substValuePlus sub nenv v
      xs' <- mapM newIdentFromIdent xs
      let nenv' = IntMap.union (IntMap.fromList (zip (map asInt xs) xs')) nenv
      e' <- substCompPlus sub nenv' e
      return (m, CompSigmaElim b xs' v' e')
    (m, CompUpIntro v) -> do
      let v' = substValuePlus sub nenv v
      return (m, CompUpIntro v')
    (m, CompUpElim x e1 e2) -> do
      e1' <- substCompPlus sub nenv e1
      x' <- newIdentFromIdent x
      let nenv' = IntMap.insert (asInt x) x' nenv
      e2' <- substCompPlus sub nenv' e2
      return (m, CompUpElim x' e1' e2')
    (m, CompEnumElim v branchList) -> do
      let v' = substValuePlus sub nenv v
      let (cs, es) = unzip branchList
      es' <- mapM (substCompPlus sub nenv) es
      return (m, CompEnumElim v' (zip cs es'))

substPrimitive :: SubstValuePlus -> NameEnv -> Primitive -> Primitive
substPrimitive sub nenv c =
  case c of
    PrimitivePrimOp op vs -> do
      let vs' = map (substValuePlus sub nenv) vs
      PrimitivePrimOp op vs'
    PrimitiveDerangement expKind ds -> do
      let ds' = map (substValuePlus sub nenv) ds
      PrimitiveDerangement expKind ds'

asIdent :: ValuePlus -> Maybe Ident
asIdent term =
  case term of
    (_, ValueVarLocal x) ->
      Just x
    _ ->
      Nothing
