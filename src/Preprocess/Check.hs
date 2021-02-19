module Preprocess.Check (check) where

import Control.Exception.Safe
import Control.Monad.State.Lazy
import Data.EnumCase
import Data.Env
import Data.Hint
import Data.Ident
import qualified Data.IntMap as IntMap
import Data.Log
import Data.Maybe (catMaybes)
import Data.MetaTerm
import qualified Data.PQueue.Min as Q
import qualified Data.Set as S
import qualified Data.Text as T

check :: Maybe Ident -> MetaTermPlus -> WithEnv ()
check mx e = do
  p "-----------------------------"
  modify (\env -> env {metaConstraintEnv = Q.empty})
  t <- infer e
  case mx of
    Just _ ->
      return ()
    Nothing ->
      insMetaConstraint t (fst e, MetaTypeNec (fst e, MetaTypeAST))
  cs <- gets metaConstraintEnv
  -- p "↓↓↓============================================"
  -- forM_ (Q.toList cs) $ \c -> do
  --   let (x, y) = toTuple c
  --   p $ T.unpack $ metaTypeToText x
  --   p $ T.unpack $ metaTypeToText y
  --   p "--------------------"
  -- p "↑↑↑↑============================================"
  sub <- unify cs
  -- p "sub:"
  -- p' sub
  -- p "---"
  -- p "result:"
  forM_ (catMaybes [mx]) $ \x -> do
    p' x
    p $ T.unpack $ metaTypeToText $ substMetaType sub t
    insMetaTypeAtTopLevel x $ substMetaType sub t

unify :: MetaConstraintQueue -> WithEnv SubstMetaType
unify q =
  case Q.getMin q of
    Nothing ->
      return IntMap.empty
    Just (MetaConstraintUnprocessed t1 t2)
      | (_, MetaTypeVar x1) <- t1,
        (_, MetaTypeVar x2) <- t2,
        x1 == x2 ->
        unify $ Q.deleteMin q
      | (_, MetaTypeVar i1) <- t1,
        ensureOccurSanity (asInt i1) t2 -> do
        -- p "updating queue with:"
        -- p' (i1, t2)
        let q' = updateQueue (IntMap.singleton (asInt i1) t2) $ Q.deleteMin q
        -- p' q'
        sub <- unify q'
        -- p "resolve:"
        -- p' (i1, t2) -- このt2も更新しないとダメ？
        -- p "before:"
        -- p' sub
        -- p "after:"
        -- p' $ compose (IntMap.singleton (asInt i1) t2) sub
        let t2' = substMetaType sub t2
        return $ compose (IntMap.singleton (asInt i1) t2') sub
      -- return $ compose (IntMap.singleton (asInt i1) t2) sub
      | (_, MetaTypeVar _) <- t2 ->
        unify $ Q.insert (MetaConstraintUnprocessed t2 t1) $ Q.deleteMin q
      | (_, MetaTypeArrow domList1 cod1) <- t1,
        (_, MetaTypeArrow domList2 cod2) <- t2,
        length domList1 == length domList2 -> do
        let foo = (MetaConstraintUnprocessed cod1 cod2) : zipWith (\d1 d2 -> MetaConstraintUnprocessed d1 d2) domList1 domList2
        unify $ Q.union (Q.fromList foo) (Q.deleteMin q)
      | (_, MetaTypeNec t1') <- t1,
        (_, MetaTypeNec t2') <- t2 ->
        unify $ Q.insert (MetaConstraintUnprocessed t1' t2') $ Q.deleteMin q
      | (_, MetaTypeInt64) <- t1,
        (_, MetaTypeInt64) <- t2 ->
        unify $ Q.deleteMin q
      | (_, MetaTypeAST) <- t1,
        (_, MetaTypeAST) <- t2 ->
        unify $ Q.deleteMin q
      | (_, MetaTypeEnum l1) <- t1,
        (_, MetaTypeEnum l2) <- t2,
        l1 == l2 ->
        unify $ Q.deleteMin q
      | otherwise -> do
        p' (t1, t2)
        unify $ Q.insert (MetaConstraintProcessed t1 t2) $ Q.deleteMin q
    Just (MetaConstraintProcessed {}) -> do
      -- p' q
      throw $ Error $ map toErrorLog (Q.toList q)

toErrorLog :: MetaConstraint -> Log
toErrorLog c = do
  let (x, y) = toTuple c
  let msg = constructErrorMsg x y
  -- let pos = supHint (fst x) (fst y) -- fixme
  logError (getPosInfo $ supHint (fst x) (fst y)) msg

ensureOccurSanity :: Int -> MetaTypePlus -> Bool
ensureOccurSanity i t =
  not (S.member i (S.map asInt $ varMetaType t))

infer :: MetaTermPlus -> WithEnv MetaTypePlus
infer term =
  case term of
    (m, MetaTermVar x) -> do
      t <- lookupMetaType m x
      return t
    (m, MetaTermImpIntro xs mRest e) -> do
      h <- newNameWith' "_"
      infer (m, MetaTermFix h xs mRest e)
    (m, MetaTermImpElim e es) -> do
      t <- infer e
      ts <- mapM infer es
      h <- newMetaTypeVar m
      insMetaConstraint t (m, MetaTypeArrow ts h)
      return h
    (m, MetaTermFix f xs mRest e) -> do
      hs <- mapM (const (newMetaTypeVar m)) xs
      forM_ (zip xs hs) $ \(x, h) -> do
        -- p "ins:"
        -- p' x
        -- p' h
        insMetaType x h
      h <- newMetaTypeVar m
      case mRest of
        Just rest -> do
          let tRest = (m, MetaTypeNec (m, MetaTypeAST))
          insMetaType rest tRest
          insMetaType f (m, MetaTypeArrow (hs ++ [tRest]) h)
          t <- infer e
          insMetaConstraint h t
          return (m, MetaTypeArrow (hs ++ [tRest]) h)
        Nothing -> do
          insMetaType f (m, MetaTypeArrow hs h)
          t <- infer e
          insMetaConstraint h t
          return (m, MetaTypeArrow hs h)
    (m, MetaTermNecIntro e) -> do
      t <- infer e
      return (m, MetaTypeNec t)
    (m, MetaTermNecElim e) -> do
      t <- infer e
      h <- newMetaTypeVar m
      insMetaConstraint (m, MetaTypeNec h) t
      return h
    (m, MetaTermLeaf _) ->
      return (m, MetaTypeAST)
    (m, MetaTermNode es) -> do
      ts <- mapM infer es
      forM_ ts $ \t ->
        insMetaConstraint t (m, MetaTypeAST)
      return (m, MetaTypeAST)
    (m, MetaTermConst c) -> do
      (is, t) <- lookupMetaConstTypeEnv m c
      instantiate m is t
    (m, MetaTermInt64 _) ->
      return (m, MetaTypeInt64)
    (m, MetaTermEnumIntro c) -> do
      k <- lookupKind m c
      return (m, MetaTypeEnum k)
    (m, MetaTermEnumElim (e, i) caseList) -> do
      t <- infer e
      insMetaConstraint t (fst e, MetaTypeVar i)
      let (cs, es) = unzip caseList
      tsC <- mapM inferEnumCase cs
      tsE <- mapM infer es
      constrainList $ t : tsC
      constrainList tsE
      if null caseList
        then newMetaTypeVar m -- ex falso quodlibet
        else return $ head tsE

lookupMetaType :: Hint -> Ident -> WithEnv MetaTypePlus
lookupMetaType m x = do
  tenv <- gets metaTypeEnv
  case IntMap.lookup (asInt x) tenv of
    Just (varList, t) ->
      instantiate m varList t
    _ -> do
      raiseCritical m $
        "the variable `" <> (asText x) <> "` is not found in the meta-type environment."

instantiate :: Hint -> [Int] -> MetaTypePlus -> WithEnv MetaTypePlus
instantiate m varList t = do
  is <- mapM (const $ newNameWith' "tvar") varList
  let sub = IntMap.fromList $ zip varList (map (\i -> (m, MetaTypeVar i)) is)
  return $ substMetaType sub t

newMetaTypeVar :: Hint -> WithEnv MetaTypePlus
newMetaTypeVar m = do
  i <- newNameWith' "tvar"
  return (m, MetaTypeVar i)

insMetaConstraint :: MetaTypePlus -> MetaTypePlus -> WithEnv ()
insMetaConstraint t1 t2 =
  modify (\env -> env {metaConstraintEnv = Q.insert (MetaConstraintUnprocessed t1 t2) (metaConstraintEnv env)})

insMetaType :: Ident -> MetaTypePlus -> WithEnv ()
insMetaType x t =
  modify (\env -> env {metaTypeEnv = IntMap.insert (asInt x) ([], t) (metaTypeEnv env)})

insMetaTypeAtTopLevel :: Ident -> MetaTypePlus -> WithEnv ()
insMetaTypeAtTopLevel x t = do
  let is = varMetaType t
  modify (\env -> env {metaTypeEnv = IntMap.insert (asInt x) (map asInt $ S.toList is, t) (metaTypeEnv env)})

constrainList :: [MetaTypePlus] -> WithEnv ()
constrainList typeList =
  case typeList of
    [] ->
      return ()
    [_] ->
      return ()
    (t1 : t2 : ts) -> do
      insMetaConstraint t1 t2
      constrainList $ t2 : ts

inferEnumCase :: EnumCasePlus -> WithEnv MetaTypePlus
inferEnumCase weakCase =
  case weakCase of
    (m, EnumCaseLabel name) -> do
      k <- lookupKind m name
      return (m, MetaTypeEnum k)
    (m, EnumCaseDefault) -> do
      h <- newMetaTypeVar m
      return h

constructErrorMsg :: MetaTypePlus -> MetaTypePlus -> T.Text
constructErrorMsg t1 t2 =
  "couldn't unify the following two meta-types:\n- "
    <> metaTypeToText t1
    <> "\n- "
    <> metaTypeToText t2

toTuple :: MetaConstraint -> (MetaTypePlus, MetaTypePlus)
toTuple c =
  case c of
    MetaConstraintUnprocessed t1 t2 ->
      (t1, t2)
    MetaConstraintProcessed t1 t2 ->
      (t1, t2)

compose :: SubstMetaType -> SubstMetaType -> SubstMetaType
compose s1 s2 =
  IntMap.union s1 $ IntMap.map (\x -> substMetaType s1 x) s2

mapMetaConstraint :: SubstMetaType -> MetaConstraint -> MetaConstraint
mapMetaConstraint sub c =
  case c of
    MetaConstraintUnprocessed t1 t2 ->
      MetaConstraintUnprocessed (substMetaType sub t1) (substMetaType sub t2)
    MetaConstraintProcessed t1 t2 ->
      MetaConstraintProcessed (substMetaType sub t1) (substMetaType sub t2)

updateQueue :: SubstMetaType -> MetaConstraintQueue -> MetaConstraintQueue
updateQueue sub q = do
  Q.fromList $ map (mapMetaConstraint sub) $ Q.toList q
