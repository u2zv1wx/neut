module Reduce.MetaTerm (reduceMetaTerm) where

import Codec.Binary.UTF8.String
import Control.Exception.Safe
import Control.Monad.State.Lazy hiding (get)
import Data.EnumCase
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Hint
import Data.Ident
import Data.Int
import qualified Data.IntMap as IntMap
import Data.Log
import Data.Maybe (catMaybes)
import Data.MetaTerm
import qualified Data.Text as T
import Data.Tree
import Text.Read (readMaybe)

reduceMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
reduceMetaTerm term =
  case term of
    (m, MetaTermImpElim e es) -> do
      e' <- reduceMetaTerm e
      es' <- mapM reduceMetaTerm es
      case e' of
        (mLam, MetaTermImpIntro xs mRest body) -> do
          h <- newNameWith' "SELF"
          reduceFix m (mLam, MetaTermFix h xs mRest body) es'
        (_, MetaTermFix {}) ->
          reduceFix m e' es'
        (_, MetaTermConst c) ->
          reduceConstApp m c es'
        _ -> do
          raiseError m $ "the term \n  " <> showAsSExp (toTree e') <> "\ncannot be applied to:\n  " <> T.intercalate "\n" (map (showAsSExp . toTree) es')
    (m, MetaTermEnumElim (e, _) caseList) -> do
      e' <- reduceMetaTerm e
      let caseList' = map (\(c, body) -> (snd c, body)) caseList
      case e' of
        (_, MetaTermEnumIntro l) ->
          case lookup (EnumCaseLabel l) caseList' of
            Just body ->
              reduceMetaTerm body
            Nothing ->
              raiseError m "found an ill-typed switch"
        _ -> do
          raiseError m "found an ill-typed switch"
    (m, MetaTermNode es) -> do
      es' <- mapM reduceMetaTerm es
      return (m, MetaTermNode es')
    _ -> do
      return term

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
    "cons"
      | [t, (_, MetaTermNode ts)] <- es ->
        return (m, MetaTermNode (t : ts))
    "dump"
      | [arg] <- es -> do
        liftIO $ putStrLn $ T.unpack $ showAsSExp $ toTree arg
        return (m, MetaTermEnumIntro "top.unit")
    "head"
      | [(mNode, MetaTermNode ts)] <- es ->
        case ts of
          h : _ ->
            return h
          _ ->
            raiseError mNode "the constant `head` cannot be applied to nil"
    "is-nil"
      | [(_, MetaTermNode ts)] <- es ->
        return $ liftBool (null ts) m
    "is-leaf"
      | [(mLeaf, MetaTermLeaf _)] <- es ->
        return $ liftBool True mLeaf
      | [(mNode, MetaTermNode _)] <- es ->
        return $ liftBool False mNode
    "is-node"
      | [(mLeaf, MetaTermLeaf _)] <- es ->
        return $ liftBool False mLeaf
      | [(mNode, MetaTermNode _)] <- es ->
        return $ liftBool True mNode
    "leaf-mul"
      | [(mLeaf, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return (mLeaf, MetaTermLeaf (s1 <> s2))
    "leaf-equal"
      | [(_, MetaTermLeaf s1), (_, MetaTermLeaf s2)] <- es ->
        return $ liftBool (s1 == s2) m
    "leaf-uncons"
      | [(mLeaf, MetaTermLeaf s)] <- es,
        Just (ch, rest) <- T.uncons s -> do
        return (mLeaf, MetaTermNode [(mLeaf, MetaTermLeaf (T.singleton ch)), (mLeaf, MetaTermLeaf rest)])
    "tail"
      | [(mNode, MetaTermNode ts)] <- es ->
        case ts of
          (_ : rest) ->
            return (mNode, MetaTermNode rest)
          _ ->
            raiseError mNode "the constant `tail` cannot be applied to nil"
    "new-symbol"
      | [] <- es -> do
        i <- newCount
        return (m, MetaTermLeaf ("#" <> T.pack (show i)))
    "nth"
      | [(_, MetaTermInt64 i), (_, MetaTermNode ts)] <- es -> do
        if 0 <= i && i < fromIntegral (length ts)
          then return $ ts !! (fromIntegral i)
          else raiseError m "index out of range"
    "string-to-u8-list"
      | [(mStr, MetaTermLeaf atom)] <- es -> do
        case readMaybe (T.unpack atom) of
          Just str -> do
            -- (string-to-u8-list "abcd") ~> (97 98 99 100)
            let u8s = encode str
            return (m, MetaTermNode (map (\i -> (mStr, MetaTermLeaf (T.pack (show i)))) u8s))
          Nothing ->
            raiseError mStr "the argument of `string-to-u8-list` must be a string"
    _
      | Just op <- toArithOp c,
        [(_, MetaTermInt64 i1), (_, MetaTermInt64 i2)] <- es ->
        return (m, MetaTermInt64 (op i1 i2))
      | Just op <- toCmpOp c,
        [(_, MetaTermInt64 i1), (_, MetaTermInt64 i2)] <- es ->
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
    (_, MetaTermInt64 _) ->
      ArgInt
    (_, MetaTermEnumIntro _) ->
      ArgEnum
    (_, _) ->
      ArgLam

matchTree :: Arg -> MetaTermPlus -> Maybe (Arg, MetaTermPlus)
matchTree argForm t =
  case (argForm, t) of
    (ArgLeaf, (_, MetaTermLeaf _)) ->
      Nothing
    (ArgNode, (_, MetaTermNode _)) ->
      Nothing
    (ArgInt, (_, MetaTermInt64 _)) ->
      Nothing
    (ArgAny, _) ->
      Nothing
    (a, e) ->
      Just (a, e)

toArithOp :: T.Text -> Maybe (Int64 -> Int64 -> Int64)
toArithOp opStr =
  case opStr of
    "int-add" ->
      Just (+)
    "int-sub" ->
      Just (-)
    "int-mul" ->
      Just (*)
    "int-div" ->
      Just div
    _ ->
      Nothing

toCmpOp :: T.Text -> Maybe (Int64 -> Int64 -> Bool)
toCmpOp opStr =
  case opStr of
    "int-gt" ->
      Just (>)
    "int-ge" ->
      Just (>=)
    "int-lt" ->
      Just (<)
    "int-le" ->
      Just (<=)
    "int-eq" ->
      Just (==)
    _ ->
      Nothing

liftBool :: Bool -> Hint -> MetaTermPlus
liftBool b m =
  if b
    then (m, MetaTermEnumIntro "bool.true")
    else (m, MetaTermEnumIntro "bool.false")
