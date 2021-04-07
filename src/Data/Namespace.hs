module Data.Namespace where

import Control.Monad.State.Lazy
import Data.Basic
import Data.Env
import qualified Data.HashMap.Lazy as Map
import Data.Log
import Data.LowType
import Data.MetaTerm
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Tree
import Data.WeakTerm hiding (asVar)

nsSepChar :: Char
nsSepChar =
  '.'

{-# INLINE nsSep #-}
nsSep :: T.Text
nsSep =
  T.singleton nsSepChar

{-# INLINE nsUnsafe #-}
nsUnsafe :: T.Text
nsUnsafe =
  "unsafe" <> nsSep

{-# INLINE nsOS #-}
nsOS :: T.Text
nsOS =
  "os" <> nsSep

use :: T.Text -> WithEnv ()
use s =
  modify (\e -> e {prefixEnv = s : prefixEnv e})

unuse :: T.Text -> WithEnv ()
unuse s =
  modify (\e -> e {prefixEnv = filter (/= s) (prefixEnv e)})

withSectionPrefix :: T.Text -> WithEnv T.Text
withSectionPrefix x = do
  ns <- gets sectionEnv
  return $ foldl (\acc n -> n <> nsSep <> acc) x ns

getCurrentSection :: WithEnv T.Text
getCurrentSection = do
  ns <- gets sectionEnv
  return $ getCurrentSection' ns

getCurrentSection' :: [T.Text] -> T.Text
getCurrentSection' nameStack =
  case nameStack of
    [] ->
      ""
    [n] ->
      n
    (n : ns) ->
      getCurrentSection' ns <> nsSep <> n

prefixTextPlus :: TreePlus -> WithEnv TreePlus
prefixTextPlus tree =
  case tree of
    (_, TreeLeaf "_") ->
      return tree
    (m, TreeLeaf x) -> do
      x' <- withSectionPrefix x
      return (m, TreeLeaf x')
    (m, TreeNode [(mx, TreeLeaf "_"), t]) ->
      return (m, TreeNode [(mx, TreeLeaf "_"), t])
    (m, TreeNode [(mx, TreeLeaf x), t]) -> do
      x' <- withSectionPrefix x
      return (m, TreeNode [(mx, TreeLeaf x'), t])
    t ->
      raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

handleSection :: T.Text -> WithEnv a -> WithEnv a
handleSection s cont = do
  modify (\e -> e {sectionEnv = s : sectionEnv e})
  getCurrentSection >>= use
  cont

handleEnd :: Hint -> T.Text -> WithEnv a -> WithEnv a
handleEnd m s cont = do
  ns <- gets sectionEnv
  case ns of
    [] ->
      raiseError m "there is no section to end"
    s' : ns'
      | s == s' -> do
        getCurrentSection >>= unuse
        modify (\e -> e {sectionEnv = ns'})
        cont
      | otherwise ->
        raiseError m $
          "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"

{-# INLINE resolveSymbol #-}
resolveSymbol :: Hint -> (T.Text -> WithEnv (Maybe b)) -> T.Text -> WithEnv (Maybe b)
resolveSymbol m predicate name = do
  candList <- constructCandList name
  candList' <- takeAll predicate candList []
  case candList' of
    [] ->
      return Nothing
    [prefixedName] ->
      predicate prefixedName
    _ -> do
      let candInfo = T.concat $ map (\cand -> "\n- " <> cand) candList'
      raiseError m $ "this `" <> name <> "` is ambiguous since it could refer to:" <> candInfo

constructCandList :: T.Text -> WithEnv [T.Text]
constructCandList name = do
  penv <- gets prefixEnv
  nenv <- gets nsEnv
  return $ constructCandList' nenv $ name : map (<> nsSep <> name) penv

constructCandList' :: [(T.Text, T.Text)] -> [T.Text] -> [T.Text]
constructCandList' nenv nameList =
  concat $ map (constructCandList'' nenv) nameList

constructCandList'' :: [(T.Text, T.Text)] -> T.Text -> [T.Text]
constructCandList'' nenv name = do
  let nameList = findNext nenv name
  if null nameList
    then [name]
    else constructCandList' nenv nameList

findNext :: [(T.Text, T.Text)] -> T.Text -> [T.Text]
findNext nenv name = do
  concat $
    concat $
      flip map nenv $ \(from, to) -> do
        case T.stripPrefix (from <> nsSep) name of
          Just suffix -> do
            return [to <> nsSep <> suffix]
          Nothing ->
            return []

takeAll :: (T.Text -> WithEnv (Maybe b)) -> [T.Text] -> [T.Text] -> WithEnv [T.Text]
takeAll predicate candidateList acc =
  case candidateList of
    [] ->
      return acc
    x : xs -> do
      mv <- predicate x
      case mv of
        Just _ ->
          takeAll predicate xs (x : acc)
        Nothing ->
          takeAll predicate xs acc

{-# INLINE asVar #-}
asVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> (Ident -> a) -> WithEnv (Maybe (Hint, a))
asVar m nenv var f =
  return $ Map.lookup var nenv >>= \x -> return (m, f x)

{-# INLINE asMetaVar #-}
asMetaVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> WithEnv (Maybe MetaTermPlus)
asMetaVar m nenv var =
  asVar m nenv var MetaTermVar

{-# INLINE asWeakVar #-}
asWeakVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> WithEnv (Maybe WeakTermPlus)
asWeakVar m nenv var =
  asVar m nenv var (WeakTermVar VarKindLocal)

{-# INLINE asItself #-}
asItself :: Hint -> Map.HashMap T.Text Ident -> T.Text -> WithEnv (Maybe (Hint, Ident))
asItself m nenv var =
  asVar m nenv var id

{-# INLINE findThenModify #-}
findThenModify :: (Env -> Map.HashMap T.Text t) -> T.Text -> (T.Text -> a) -> WithEnv (Maybe a)
findThenModify info name f = do
  env <- gets info
  if name `Map.member` env
    then return $ Just $ f name
    else return Nothing

{-# INLINE asWeakEnumValue #-}
asWeakEnumValue :: Hint -> T.Text -> WithEnv (Maybe WeakTermPlus)
asWeakEnumValue m name = do
  findThenModify revEnumEnv name (\x -> (m, WeakTermEnumIntro x))

{-# INLINE asWeakEnumType #-}
asWeakEnumType :: Hint -> T.Text -> WithEnv (Maybe WeakTermPlus)
asWeakEnumType m name = do
  findThenModify enumEnv name (\x -> (m, WeakTermEnum x))

{-# INLINE asEnumCase #-}
asEnumCase :: T.Text -> WithEnv (Maybe EnumCase)
asEnumCase name =
  findThenModify revEnumEnv name EnumCaseLabel

{-# INLINE asMetaConstant #-}
asMetaConstant :: Hint -> T.Text -> Maybe MetaTermPlus
asMetaConstant m name =
  if Map.member name metaConstants
    then Just (m, MetaTermConst name)
    else Nothing

{-# INLINE asWeakConstant #-}
asWeakConstant :: Hint -> T.Text -> WithEnv (Maybe WeakTermPlus)
asWeakConstant m name
  | Just (LowTypeInt _) <- asLowTypeMaybe name =
    return $ Just (m, WeakTermConst name)
  | Just (LowTypeFloat _) <- asLowTypeMaybe name =
    return $ Just (m, WeakTermConst name)
  | Just _ <- asPrimOp name =
    return $ Just (m, WeakTermConst name)
  | otherwise = do
    set <- gets constantSet
    if S.member name set
      then return $ Just (m, WeakTermConst name)
      else return Nothing

-- {-# INLINE asWeakConstant #-}
-- asWeakConstant :: Hint -> T.Text -> Maybe WeakTermPlus
-- asWeakConstant m name
--   | Just (LowTypeInt _) <- asLowTypeMaybe name =
--     Just (m, WeakTermConst name)
--   | Just (LowTypeFloat _) <- asLowTypeMaybe name =
--     Just (m, WeakTermConst name)
--   | Just _ <- asPrimOp name =
--     Just (m, WeakTermConst name)
--   | otherwise =
--     Nothing

tryCand :: (Monad m) => m (Maybe a) -> m a -> m a
tryCand comp cont = do
  mx <- comp
  case mx of
    Just x ->
      return x
    Nothing ->
      cont
