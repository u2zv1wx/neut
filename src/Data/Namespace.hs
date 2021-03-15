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
import Data.WeakTerm

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

resolveSymbol :: (T.Text -> WithEnv (Maybe b)) -> T.Text -> WithEnv (Maybe b)
resolveSymbol predicate name = do
  penv <- gets prefixEnv
  takeFirst predicate $ (map (\prefix -> prefix <> nsSep <> name) penv) ++ [name]

-- takeFirst predicate $ name : (map (\prefix -> prefix <> nsSep <> name) penv)

takeFirst :: (a -> WithEnv (Maybe b)) -> [a] -> WithEnv (Maybe b)
takeFirst predicate candidateList =
  case candidateList of
    [] ->
      return Nothing
    x : xs -> do
      mv <- predicate x
      case mv of
        Just v ->
          return $ Just v
        Nothing ->
          takeFirst predicate xs

asVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> (Ident -> a) -> WithEnv (Maybe (Hint, a))
asVar m nenv var f =
  return $ Map.lookup var nenv >>= \x -> return (m, f x)

asMetaVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> WithEnv (Maybe MetaTermPlus)
asMetaVar m nenv var =
  asVar m nenv var MetaTermVar

asWeakVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> WithEnv (Maybe WeakTermPlus)
asWeakVar m nenv var =
  asVar m nenv var WeakTermUpsilon

findThenModify :: (Env -> Map.HashMap T.Text t) -> T.Text -> (T.Text -> a) -> WithEnv (Maybe a)
findThenModify info name f = do
  env <- gets info
  if name `Map.member` env
    then return $ Just $ f name
    else return Nothing

asWeakEnumValue :: Hint -> T.Text -> WithEnv (Maybe WeakTermPlus)
asWeakEnumValue m name = do
  findThenModify revEnumEnv name (\x -> (m, WeakTermEnumIntro x))

asWeakEnumType :: Hint -> T.Text -> WithEnv (Maybe WeakTermPlus)
asWeakEnumType m name = do
  findThenModify enumEnv name (\x -> (m, WeakTermEnum x))

asEnumCase :: T.Text -> WithEnv (Maybe EnumCase)
asEnumCase name =
  findThenModify revEnumEnv name EnumCaseLabel

asMetaConstant :: Hint -> T.Text -> WithEnv (Maybe MetaTermPlus)
asMetaConstant m name =
  if Map.member name metaConstants
    then return $ Just (m, MetaTermConst name)
    else return Nothing

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

tryCand :: (Monad m) => m (Maybe a) -> m a -> m a
tryCand comp cont = do
  mx <- comp
  case mx of
    Just x ->
      return x
    Nothing ->
      cont
