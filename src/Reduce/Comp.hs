module Reduce.Comp
  ( reduceCompPlus,
  )
where

import Control.Monad.State.Lazy
import Data.Comp
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap

reduceCompPlus :: CompPlus -> WithEnv CompPlus
reduceCompPlus term =
  case term of
    (m, CompPrimitive c) ->
      return (m, CompPrimitive c)
    (m, CompPiElimDownElim v ds) -> do
      cenv <- gets codeEnv
      case v of
        (_, ValueConst x)
          | Just (Definition (IsFixed False) xs body) <- Map.lookup x cenv,
            length xs == length ds -> do
            let sub = IntMap.fromList (zip (map asInt xs) ds)
            reduceCompPlus $ substCompPlus sub body
        _ ->
          return (m, CompPiElimDownElim v ds)
    (m, CompSigmaElim xs v e) ->
      case v of
        (_, ValueSigmaIntro ds)
          | length ds == length xs -> do
            let sub = IntMap.fromList (zip (map asInt xs) ds)
            reduceCompPlus $ substCompPlus sub e
        _ -> do
          e' <- reduceCompPlus e
          case e' of
            (mUp, CompUpIntro (_, ValueSigmaIntro ds))
              | Just ys <- mapM asUpsilon ds,
                xs == ys ->
                return (mUp, CompUpIntro v) -- eta-reduce
            _ ->
              return (m, CompSigmaElim xs v e')
    (m, CompUpIntro v) ->
      return (m, CompUpIntro v)
    (m, CompUpElim x e1 e2) -> do
      e1' <- reduceCompPlus e1
      case e1' of
        (mUp, CompUpIntro d)
          | metaIsReducible mUp -> do
            let sub = IntMap.fromList [(asInt x, d)]
            reduceCompPlus $ substCompPlus sub e2
        (my, CompUpElim y ey1 ey2) ->
          reduceCompPlus (my, CompUpElim y ey1 (m, CompUpElim x ey2 e2)) -- commutative conversion
        (my, CompSigmaElim yts vy ey) ->
          reduceCompPlus (my, CompSigmaElim yts vy (m, CompUpElim x ey e2)) -- commutative conversion
          -- (my, CompStructElim yts vy ey) ->
          --   reduceCompPlus (my, CompStructElim yts vy (m, CompUpElim x ey e2)) -- commutative conversion
        _ -> do
          e2' <- reduceCompPlus e2
          case e2' of
            (_, CompUpIntro (_, ValueUpsilon y))
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

-- (m, CompStructElim xks d e) -> do
--   let (xs, ks1) = unzip xks
--   case d of
--     (_, ValueStructIntro eks)
--       | (es, ks2) <- unzip eks,
--         ks1 == ks2 -> do
--         let sub = IntMap.fromList (zip (map asInt xs) es)
--         reduceCompPlus $ substCompPlus sub e
--     _ -> do
--       e' <- reduceCompPlus e
--       case e' of
--         (mUp, CompUpIntro (_, ValueStructIntro dks))
--           | (ds2, ks2) <- unzip dks,
--             ks1 == ks2,
--             Just ys <- mapM asUpsilon ds2,
--             xs == ys ->
--             return (mUp, CompUpIntro d) -- eta-reduce
--         _ ->
--           return (m, CompStructElim xks d e')
