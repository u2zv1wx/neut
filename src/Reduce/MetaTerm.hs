module Reduce.MetaTerm
  ( reduceMetaTerm,
  )
where

import Codec.Binary.UTF8.String
import Control.Exception.Safe
import Control.Monad.State.Lazy hiding (get)
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import qualified Data.IntMap as IntMap
import Data.Log
import Data.Maybe (catMaybes)
import Data.MetaTerm
import qualified Data.Text as T
import Data.Tree
import Text.Read (readMaybe)

-- bottleneck (13 ~ 18%)
reduceMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
reduceMetaTerm term =
  case term of
    (m, MetaTermImpElim e es) -> do
      e' <- reduceMetaTerm e
      es' <- mapM reduceMetaTerm es
      case e' of
        (_, MetaTermImpIntro xs mRest body)
          | Just rest <- mRest -> do
            if length xs > length es'
              then raiseError m $ "the function here must be called with x (>= " <> T.pack (show (length xs)) <> ") arguments, but found " <> T.pack (show (length es'))
              else do
                let (es1, es2) = splitAt (length xs) es'
                let restArg = (m, MetaTermNode es2)
                let sub = IntMap.fromList $ zip (map asInt xs) es1 ++ [(asInt rest, restArg)]
                reduceMetaTerm $ substMetaTerm sub body
          | otherwise -> do
            if length xs /= length es'
              then raiseArityMismatch m (length xs) (length es')
              else do
                let sub = IntMap.fromList $ zip (map asInt xs) es'
                reduceMetaTerm $ substMetaTerm sub body
        (_, MetaTermFix {}) ->
          reduceFix m e' es'
        (_, MetaTermConst c) ->
          reduceConstApp m c es'
        _ -> do
          raiseError m $ "the term \n  " <> showAsSExp (toTree e') <> "\ncannot be applied to:\n  " <> T.intercalate "\n" (map (showAsSExp . toTree) es')
    (m, MetaTermNode es) -> do
      es' <- mapM reduceMetaTerm es
      return $ (m, MetaTermNode es')
    (_, MetaTermIf cond onTrue onFalse) -> do
      cond' <- reduceMetaTerm cond
      case cond' of
        (_, MetaTermNode []) ->
          reduceMetaTerm onFalse
        _ ->
          reduceMetaTerm onTrue
    _ ->
      return term

{-# INLINE reduceFix #-}
reduceFix :: Hint -> MetaTermPlus -> [MetaTermPlus] -> WithEnv MetaTermPlus
reduceFix m e es =
  case e of
    (_, MetaTermFix f xs mRest (_, body))
      | Just rest <- mRest -> do
        if length xs > length es
          then raiseError m $ "the function here must be called with x (>= " <> T.pack (show (length xs)) <> ") arguments, but found " <> T.pack (show (length es))
          else do
            let es1 = take (length xs) es
            let restArg = (m, MetaTermNode (drop (length xs) es))
            let sub = IntMap.fromList $ (asInt f, e) : zip (map asInt xs) es1 ++ [(asInt rest, restArg)]
            reduceMetaTerm $ substMetaTerm sub (m, body)
      | otherwise -> do
        if length xs /= length es
          then raiseArityMismatch m (length xs) (length es)
          else do
            let sub = IntMap.fromList $ (asInt f, e) : zip (map asInt xs) es
            reduceMetaTerm $ substMetaTerm sub (m, body)
    _ ->
      raiseCritical (fst e) "unreachable"

raiseArityMismatch :: Hint -> Int -> Int -> WithEnv a
raiseArityMismatch m expected found = do
  case expected of
    0 ->
      raiseError m $ "the function here must be called with 0 argument, but found " <> T.pack (show found)
    1 ->
      raiseError m $ "the function here must be called with 1 argument, but found " <> T.pack (show found)
    _ ->
      raiseError m $ "the function here must be called with " <> T.pack (show expected) <> " arguments, but found " <> T.pack (show found)

reduceConstApp :: Hint -> T.Text -> [MetaTermPlus] -> WithEnv MetaTermPlus
reduceConstApp m c es =
  case c of
    "meta.dump"
      | [arg] <- es -> do
        liftIO $ putStrLn $ T.unpack $ showAsSExp $ toTree arg
        return (m, MetaTermLeaf "true")
    "meta.is-nil"
      | [(_, MetaTermNode ts)] <- es ->
        return $ liftBool (null ts) m
    "meta.is-leaf"
      | [(mLeaf, MetaTermLeaf _)] <- es ->
        return $ liftBool True mLeaf
      | [(mNode, MetaTermNode _)] <- es ->
        return $ liftBool False mNode
    "meta.is-node"
      | [(mLeaf, MetaTermLeaf _)] <- es ->
        return $ liftBool False mLeaf
      | [(mNode, MetaTermNode _)] <- es ->
        return $ liftBool True mNode
    "meta.leaf.equal"
      | [(_, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return $ liftBool (s1 == s2) m
    "meta.leaf.from-int"
      | [(mInt, MetaTermInteger x)] <- es ->
        return (mInt, MetaTermLeaf (T.pack (show x)))
    "meta.leaf.mul"
      | [(mLeaf, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return (mLeaf, MetaTermLeaf (s1 <> s2))
    "meta.leaf.new-symbol"
      | [(_, MetaTermLeaf s)] <- es -> do
        i <- newCount
        return (m, MetaTermLeaf (s <> "#" <> T.pack (show i)))
    "meta.leaf.string-to-u8-list"
      | [(mStr, MetaTermLeaf atom)] <- es -> do
        case readMaybe (T.unpack atom) of
          Just str -> do
            -- (string-to-u8-list "abcd") ~> (97 98 99 100)
            let u8s = encode str
            return (m, MetaTermNode (map (\i -> (mStr, MetaTermLeaf (T.pack (show i)))) u8s))
          Nothing ->
            raiseError mStr "the argument of `string-to-u8-list` must be a string"
    "meta.leaf.uncons"
      | [(mLeaf, MetaTermLeaf s)] <- es,
        Just (ch, rest) <- T.uncons s -> do
        return (mLeaf, MetaTermNode [(mLeaf, MetaTermLeaf (T.singleton ch)), (mLeaf, MetaTermLeaf rest)])
    "meta.node.cons"
      | [t, (_, MetaTermNode ts)] <- es ->
        return (m, MetaTermNode (t : ts))
    "meta.node.head"
      | [(mNode, MetaTermNode ts)] <- es ->
        case ts of
          h : _ ->
            return h
          _ ->
            raiseError mNode "the constant `head` cannot be applied to nil"
    "meta.node.tail"
      | [(mNode, MetaTermNode ts)] <- es ->
        case ts of
          (_ : rest) ->
            return (mNode, MetaTermNode rest)
          _ ->
            raiseError mNode "the constant `tail` cannot be applied to nil"
    _
      | Just op <- toArithOp c,
        [(_, MetaTermInteger i1), (_, MetaTermInteger i2)] <- es ->
        return (m, MetaTermInteger (op i1 i2))
      | Just op <- toCmpOp c,
        [(_, MetaTermInteger i1), (_, MetaTermInteger i2)] <- es ->
        return $ liftBool (op i1 i2) m
      | otherwise -> do
        raiseConstAppError m c es

raiseConstAppError :: Hint -> T.Text -> [MetaTermPlus] -> WithEnv a
raiseConstAppError m c es = do
  case Map.lookup c metaConstants of
    Nothing ->
      raiseCritical m $ "the constant " <> c <> " isn't in the meta-constant map (compiler bug)"
    Just argInfo ->
      if length argInfo /= length es
        then raiseArityMismatch m (length argInfo) (length es)
        else do
          let hs = catMaybes $ zipWith matchTree argInfo es
          let logList = map (\(expectedForm, e) -> toConstError expectedForm e) hs
          throw $ Error logList

toConstError :: Arg -> MetaTermPlus -> Log
toConstError argForm e =
  logError (getPosInfo (fst e)) $ "the term here is expected to be a `" <> showArgForm argForm <> "`, but it is actually a `" <> showArgForm (toArgForm e) <> "`."

toArgForm :: MetaTermPlus -> Arg
toArgForm e =
  case e of
    (_, MetaTermLeaf _) ->
      ArgLeaf
    (_, MetaTermNode _) ->
      ArgNode
    (_, MetaTermInteger _) ->
      ArgInt
    (_, _) ->
      ArgLam

matchTree :: Arg -> MetaTermPlus -> Maybe (Arg, MetaTermPlus)
matchTree argForm t =
  case (argForm, t) of
    (ArgLeaf, (_, MetaTermLeaf _)) ->
      Nothing
    (ArgNode, (_, MetaTermNode _)) ->
      Nothing
    (ArgInt, (_, MetaTermInteger _)) ->
      Nothing
    (ArgAny, _) ->
      Nothing
    (a, e) ->
      Just (a, e)

toArithOp :: T.Text -> Maybe (Integer -> Integer -> Integer)
toArithOp opStr =
  case opStr of
    "meta.int.add" ->
      Just (+)
    "meta.int.sub" ->
      Just (-)
    "meta.int.mul" ->
      Just (*)
    "meta.int.div" ->
      Just div
    _ ->
      Nothing

toCmpOp :: T.Text -> Maybe (Integer -> Integer -> Bool)
toCmpOp opStr =
  case opStr of
    "meta.int.gt" ->
      Just (>)
    "meta.int.ge" ->
      Just (>=)
    "meta.int.lt" ->
      Just (<)
    "meta.int.le" ->
      Just (<=)
    "meta.int.eq" ->
      Just (==)
    _ ->
      Nothing

liftBool :: Bool -> Hint -> MetaTermPlus
liftBool b m =
  if b
    then (m, MetaTermLeaf "true")
    else (m, MetaTermNode [])
