module Reduce.MetaTerm where

import Control.Monad.IO.Class
import Data.EnumCase
import Data.Env
import Data.Hint
import Data.Ident
import Data.Int
import qualified Data.IntMap as IntMap
import Data.MetaTerm
import qualified Data.Text as T
import Data.Tree
import Preprocess.Discern
import Preprocess.Reflect

reduceMetaTerm :: MetaTermPlus -> WithEnv MetaTermPlus
reduceMetaTerm term =
  case term of
    (m, MetaTermImpElim e es) -> do
      e' <- reduceMetaTerm e
      es' <- mapM reduceMetaTerm es
      case e' of
        (_, MetaTermImpIntro xs body)
          | length xs == length es' -> do
            let sub = IntMap.fromList $ zip (map asInt xs) es'
            reduceMetaTerm $ substMetaTerm sub body
        (_, MetaTermFix f xs body)
          | length xs == length es' -> do
            let sub = IntMap.fromList $ (asInt f, e') : zip (map asInt xs) es'
            reduceMetaTerm $ substMetaTerm sub body
        (_, MetaTermConst c)
          | "meta-print" == c,
            [arg] <- es' -> do
            liftIO $ putStrLn $ T.unpack $ showAsSExp $ reify arg
            return (m, MetaTermEnumIntro "top.unit")
          | "meta-cons" == c -> do
            case es' of
              [(_, MetaTermNecIntro t), (_, MetaTermNecIntro (_, MetaTermNode ts))] ->
                return (m, MetaTermNecIntro (m, MetaTermNode (t : ts)))
              _ ->
                raiseError m $ "meta-cons"
          | "meta-head" == c,
            [arg] <- es' -> do
            case arg of
              (mQuote, MetaTermNecIntro (_, MetaTermNode (h : _))) ->
                return (mQuote, MetaTermNecIntro h)
              _ ->
                raiseError m $ "meta-head cannot be applied to: " <> showAsSExp (reify arg)
          | "meta-tail" == c,
            [arg] <- es' -> do
            case arg of
              (mQuote, MetaTermNecIntro (mNode, MetaTermNode (_ : rest))) ->
                return (mQuote, MetaTermNecIntro (mNode, MetaTermNode rest))
              _ ->
                raiseError m $ "meta-tail cannot be applied to: " <> showAsSExp (reify arg)
          | "meta-empty?" == c,
            [arg] <- es' -> do
            case arg of
              (_, MetaTermNecIntro (_, MetaTermNode ts)) ->
                return $ liftBool (null ts) m
              _ ->
                raiseError m $ "meta-empty? cannot be applied to: " <> showAsSExp (reify arg)
          | "evaluate" == c -> do
            case es' of
              [arg] ->
                case arg of
                  (_, MetaTermNecIntro t) -> do
                    reflect (reify t) >>= discernMetaTerm >>= reduceMetaTerm
                  _ ->
                    raiseError m $ "evaluate cannot be applied to: " <> showAsSExp (reify arg)
              _ ->
                raiseError m "arity mismatch"
          | "meta-join-symbol" == c,
            [arg1, arg2] <- es' -> do
            case (arg1, arg2) of
              ((mQuote, MetaTermNecIntro (mLeaf, MetaTermLeaf s1)), (_, MetaTermNecIntro (_, MetaTermLeaf s2))) ->
                return (mQuote, MetaTermNecIntro (mLeaf, MetaTermLeaf (s1 <> s2)))
              _ ->
                raiseError m $ "meta-join cannot be applied to: (this)"
          | "meta-leaf-eq" == c,
            [arg1, arg2] <- es' -> do
            case (arg1, arg2) of
              ((_, MetaTermNecIntro (_, MetaTermLeaf s1)), (_, MetaTermNecIntro (_, MetaTermLeaf s2))) ->
                return $ liftBool (s1 == s2) m
              _ ->
                raiseError m $ "meta-leaf-eq cannot be applied to: (this)"
          | Just op <- toArithmeticOperator c,
            [arg1, arg2] <- es' -> do
            case (arg1, arg2) of
              ((_, MetaTermInt64 i1), (_, MetaTermInt64 i2)) ->
                return (m, MetaTermInt64 (op i1 i2))
              _ ->
                raiseError m "found an ill-typed application"
          | Just op <- toCmpOp c -> do
            case es' of
              [(_, MetaTermInt64 i1), (_, MetaTermInt64 i2)] ->
                return $ liftBool (op i1 i2) m
              _ ->
                raiseError m $ "found an ill-typed application of a metaconstant " <> c
          | otherwise ->
            raiseError m $ "undefined meta-constant: " <> c
        _ ->
          raiseError m "arity mismatch"
    (m, MetaTermEnumElim e caseList) -> do
      e' <- reduceMetaTerm e
      let caseList' = map (\(c, body) -> (snd c, body)) caseList
      case e' of
        (_, MetaTermEnumIntro l) ->
          case lookup (EnumCaseLabel l) caseList' of
            Just body ->
              reduceMetaTerm body
            Nothing ->
              raiseError m "found an ill-typed switch"
        _ ->
          raiseError m "found an ill-typed switch"
    (_, MetaTermNecElim e) -> do
      e' <- reduceMetaTerm e
      case e' of
        (_, MetaTermNecIntro e'') ->
          reduceMetaTerm e''
        (m, _) ->
          raiseError m "the inner term of an unquote must be a quoted term"
    (m, MetaTermNode es) -> do
      es' <- mapM reduceMetaTerm es
      return (m, MetaTermNode es')
    _ ->
      return term

toArithmeticOperator :: T.Text -> Maybe (Int64 -> Int64 -> Int64)
toArithmeticOperator opStr =
  case opStr of
    "meta-add" ->
      Just (+)
    "meta-sub" ->
      Just (-)
    "meta-mul" ->
      Just (*)
    "meta-div" ->
      Just div
    _ ->
      Nothing

toCmpOp :: T.Text -> Maybe (Int64 -> Int64 -> Bool)
toCmpOp opStr =
  case opStr of
    "meta-int-gt" ->
      Just (<)
    "meta-int-ge" ->
      Just (<=)
    "meta-int-lt" ->
      Just (>)
    "meta-int-le" ->
      Just (>=)
    "meta-int-eq" ->
      Just (==)
    _ ->
      Nothing

reinterpret :: MetaTermPlus -> WithEnv TreePlus
reinterpret term =
  case term of
    (m, MetaTermLeaf x) ->
      return (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      es' <- mapM reinterpret es
      return (m, TreeNode es')
    (m, _) ->
      raiseError m "the argument isn't a valid AST"

reify :: MetaTermPlus -> TreePlus
reify term =
  case term of
    (m, MetaTermVar x) ->
      (m, TreeLeaf $ asText' x) -- ホントはmeta専用の名前にするべき
    (m, MetaTermImpIntro xs e) -> do
      let e' = reify e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf "lambda"), (m, TreeNode xs'), e'])
    (m, MetaTermImpElim e es) -> do
      let e' = reify e
      let es' = map reify es
      (m, TreeNode ((m, TreeLeaf "apply") : e' : es'))
    (m, MetaTermFix f xs e) -> do
      let e' = reify e
      let xs' = map (\i -> (m, TreeLeaf $ asText' i)) xs
      (m, TreeNode [(m, TreeLeaf (asText' f)), (m, TreeNode xs'), e'])
    (m, MetaTermNecIntro e) -> do
      let e' = reify e
      (m, TreeNode [(m, TreeLeaf "quote"), e'])
    (m, MetaTermNecElim e) -> do
      let e' = reify e
      (m, TreeNode [(m, TreeLeaf "unquote"), e'])
    (m, MetaTermLeaf x) ->
      (m, TreeLeaf x)
    (m, MetaTermNode es) -> do
      let es' = map reify es
      (m, TreeNode es')
    (m, MetaTermConst c) ->
      (m, TreeLeaf c)
    (m, MetaTermInt64 i) ->
      (m, TreeLeaf $ T.pack $ show i)
    (m, MetaTermEnumIntro a) ->
      (m, TreeLeaf a)
    (m, MetaTermEnumElim e caseList) -> do
      let e' = reify e
      let (cs, bodyList) = unzip caseList
      let cs' = map reifyEnumCase cs
      let bodyList' = map reify bodyList
      let caseList' = map (\(c, body) -> (m, TreeNode [c, body])) $ zip cs' bodyList'
      (m, TreeNode [(m, TreeLeaf "switch"), e', (m, TreeNode caseList')])

reifyEnumCase :: EnumCasePlus -> TreePlus
reifyEnumCase (m, v) =
  case v of
    EnumCaseLabel l ->
      (m, TreeLeaf l)
    EnumCaseDefault ->
      (m, TreeLeaf "default")

liftBool :: Bool -> Hint -> MetaTermPlus
liftBool b m =
  if b
    then (m, MetaTermEnumIntro "bool.true")
    else (m, MetaTermEnumIntro "bool.false")
