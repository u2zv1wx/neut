module Reduce.Code
  ( reduceCodePlus,
  )
where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Code
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import qualified Data.Set as S

reduceCodePlus :: CodePlus -> WithEnv CodePlus
reduceCodePlus term =
  case term of
    (m, CodeConst c) ->
      return (m, CodeConst c)
    (m, CodePiElimDownElim v ds) -> do
      cenv <- gets codeEnv
      ns <- gets nameSet
      case v of
        (_, DataConst x)
          | Just (Definition (IsFixed False) xs body) <- Map.lookup x cenv,
            length xs == length ds -> do
            let sub = IntMap.fromList (zip (map asInt xs) ds)
            reduceCodePlus $ substCodePlus sub body
        (_, DataConst x)
          | Just (Definition (IsFixed True) xs body) <- Map.lookup x cenv,
            length xs == length ds,
            not (x `S.member` ns) -> do
            modify (\env -> env {nameSet = S.insert x ns})
            body' <- reduceCodePlus body
            let def = Definition (IsFixed True) xs body'
            modify (\env -> env {codeEnv = Map.insert x def cenv})
            return (m, CodePiElimDownElim v ds)
        _ ->
          return (m, CodePiElimDownElim v ds)
    (m, CodeSigmaElim mk xs v e) ->
      case v of
        (_, DataSigmaIntro mk' ds)
          | length ds == length xs,
            mk == mk' -> do
            let sub = IntMap.fromList (zip (map asInt xs) ds)
            reduceCodePlus $ substCodePlus sub e
        _ -> do
          e' <- reduceCodePlus e
          case e' of
            (mUp, CodeUpIntro (_, DataSigmaIntro _ ds))
              | Just ys <- mapM asUpsilon ds,
                xs == ys ->
                return (mUp, CodeUpIntro v) -- eta-reduce
            _ ->
              return (m, CodeSigmaElim mk xs v e')
    (m, CodeUpIntro v) ->
      return (m, CodeUpIntro v)
    (m, CodeUpElim x e1 e2) -> do
      e1' <- reduceCodePlus e1
      case e1' of
        (mUp, CodeUpIntro d)
          | metaIsReducible mUp -> do
            let sub = IntMap.fromList [(asInt x, d)]
            reduceCodePlus $ substCodePlus sub e2
        (my, CodeUpElim y ey1 ey2) ->
          reduceCodePlus (my, CodeUpElim y ey1 (m, CodeUpElim x ey2 e2)) -- commutative conversion
        (my, CodeSigmaElim mk yts vy ey) ->
          reduceCodePlus (my, CodeSigmaElim mk yts vy (m, CodeUpElim x ey e2)) -- commutative conversion
        (my, CodeStructElim yts vy ey) ->
          reduceCodePlus (my, CodeStructElim yts vy (m, CodeUpElim x ey e2)) -- commutative conversion
        _ -> do
          e2' <- reduceCodePlus e2
          case e2' of
            (_, CodeUpIntro (_, DataUpsilon y))
              | x == y -> return e1' -- eta-reduce
            _ -> return (m, CodeUpElim x e1' e2')
    (m, CodeEnumElim varInfo v les) ->
      case v of
        (_, DataEnumIntro l) ->
          case lookup (CaseValue l) les of
            Just body -> reduceCodePlus $ substCodePlus varInfo body
            Nothing ->
              case lookup CaseDefault les of
                Just body -> reduceCodePlus $ substCodePlus varInfo body
                Nothing -> return (m, CodeEnumElim varInfo v les)
        _ -> return (m, CodeEnumElim varInfo v les)
    (m, CodeStructElim xks d e) -> do
      let (xs, ks1) = unzip xks
      case d of
        (_, DataStructIntro eks)
          | (es, ks2) <- unzip eks,
            ks1 == ks2 -> do
            let sub = IntMap.fromList (zip (map asInt xs) es)
            reduceCodePlus $ substCodePlus sub e
        _ -> do
          e' <- reduceCodePlus e
          case e' of
            (mUp, CodeUpIntro (_, DataStructIntro dks))
              | (ds2, ks2) <- unzip dks,
                ks1 == ks2,
                Just ys <- mapM asUpsilon ds2,
                xs == ys ->
                return (mUp, CodeUpIntro d) -- eta-reduce
            _ -> return (m, CodeStructElim xks d e')
    (m, CodeCase sub d mces) -> do
      let (mcs, es) = unzip mces
      let es' = map (substCodePlus sub) es
      es'' <- mapM reduceCodePlus es'
      return (m, CodeCase IntMap.empty d $ zip mcs es'')
