module Data.Namespace where

import Data.Basic
import Data.Global
import qualified Data.HashMap.Lazy as Map
import Data.IORef
import Data.Log
import Data.LowType
import qualified Data.Text as T
import Data.WeakTerm hiding (asVar)
import Path

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

use :: T.Text -> IO ()
use s =
  modifyIORef' prefixEnv $ \env -> s : env

unuse :: T.Text -> IO ()
unuse s =
  modifyIORef' prefixEnv $ \env -> filter (/= s) env

withSectionPrefix :: T.Text -> IO T.Text
withSectionPrefix x = do
  ns <- readIORef sectionEnv
  return $ foldl (\acc n -> n <> nsSep <> acc) x ns

getCurrentSection :: IO T.Text
getCurrentSection = do
  ns <- readIORef sectionEnv
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

-- prefixTextPlus :: TreePlus -> IO TreePlus
-- prefixTextPlus tree =
--   case tree of
--     (_, TreeLeaf "_") ->
--       return tree
--     (m, TreeLeaf x) -> do
--       x' <- withSectionPrefix x
--       return (m, TreeLeaf x')
--     (m, TreeNode [(mx, TreeLeaf "_"), t]) ->
--       return (m, TreeNode [(mx, TreeLeaf "_"), t])
--     (m, TreeNode [(mx, TreeLeaf x), t]) -> do
--       x' <- withSectionPrefix x
--       return (m, TreeNode [(mx, TreeLeaf x'), t])
--     t ->
--       raiseSyntaxError (fst t) "LEAF | (LEAF TREE)"

handleSection :: T.Text -> IO ()
handleSection s = do
  modifyIORef' sectionEnv $ \env -> s : env

-- getCurrentSection >>= use
-- cont

-- handleSection :: T.Text -> IO a -> IO a
-- handleSection s cont = do
--   modifyIORef' sectionEnv $ \env -> s : env
--   getCurrentSection >>= use
--   cont

handleEnd :: Hint -> T.Text -> IO ()
handleEnd m s = do
  ns <- readIORef sectionEnv
  case ns of
    [] ->
      raiseError m "there is no section to end"
    s' : ns'
      | s == s' -> do
        getCurrentSection >>= unuse
        modifyIORef' sectionEnv $ \_ -> ns'
      | otherwise ->
        raiseError m $
          "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"

-- handleEnd :: Hint -> T.Text -> IO a -> IO a
-- handleEnd m s cont = do
--   ns <- readIORef sectionEnv
--   case ns of
--     [] ->
--       raiseError m "there is no section to end"
--     s' : ns'
--       | s == s' -> do
--         getCurrentSection >>= unuse
--         modifyIORef' sectionEnv $ \_ -> ns'
--         cont
--       | otherwise ->
--         raiseError m $
--           "the innermost section is not `" <> s <> "`, but is `" <> s' <> "`"

{-# INLINE resolveSymbol #-}
resolveSymbol :: Hint -> (T.Text -> Maybe b) -> T.Text -> IO (Maybe b)
resolveSymbol m predicate name = do
  candList <- constructCandList name
  case takeAll predicate candList [] of
    [] ->
      return Nothing
    [prefixedName] ->
      return $ predicate prefixedName
    candList' -> do
      let candInfo = T.concat $ map (\cand -> "\n- " <> cand) candList'
      raiseError m $ "this `" <> name <> "` is ambiguous since it could refer to:" <> candInfo

constructCandList :: T.Text -> IO [T.Text]
constructCandList name = do
  penv <- readIORef prefixEnv
  nenv <- readIORef nsEnv
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

takeAll :: (T.Text -> Maybe b) -> [T.Text] -> [T.Text] -> [T.Text]
takeAll predicate candidateList acc =
  case candidateList of
    [] ->
      acc
    x : xs -> do
      case predicate x of
        Just _ ->
          takeAll predicate xs (x : acc)
        Nothing ->
          takeAll predicate xs acc

{-# INLINE asVar #-}
asVar :: Hint -> Map.HashMap T.Text b -> T.Text -> (b -> a) -> Maybe (Hint, a)
asVar m nenv var f =
  Map.lookup var nenv >>= \x -> return (m, f x)

-- {-# INLINE asMetaVar #-}
-- asMetaVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> Maybe MetaTermPlus
-- asMetaVar m nenv var =
--   asVar m nenv var MetaTermVar

{-# INLINE asWeakVar #-}
asWeakVar :: Hint -> Map.HashMap T.Text Ident -> T.Text -> Maybe WeakTermPlus
asWeakVar m nenv var =
  asVar m nenv var (WeakTermVar VarKindLocal)

{-# INLINE asTransparentGlobalVar #-}
asTransparentGlobalVar :: Hint -> Map.HashMap T.Text (Path Abs File, Ident) -> T.Text -> Maybe WeakTermPlus
asTransparentGlobalVar m nenv var =
  asVar m nenv var (\(fp, x) -> WeakTermVar (VarKindGlobalTransparent fp) x)

{-# INLINE asOpaqueGlobalVar #-}
asOpaqueGlobalVar :: Hint -> Map.HashMap T.Text (Path Abs File, Ident) -> T.Text -> Maybe WeakTermPlus
asOpaqueGlobalVar m nenv var =
  asVar m nenv var (\(fp, x) -> WeakTermVar (VarKindGlobalOpaque fp) x)

{-# INLINE asConstructor #-}
asConstructor :: Hint -> Map.HashMap T.Text (Path Abs File, Ident) -> T.Text -> Maybe (Hint, Ident)
asConstructor m nenv var =
  asVar m nenv var snd

{-# INLINE findThenModify #-}
findThenModify :: Map.HashMap T.Text t -> (T.Text -> a) -> T.Text -> Maybe a
findThenModify env f name = do
  if name `Map.member` env
    then Just $ f name
    else Nothing

{-# INLINE asEnumLabel #-}
asEnumLabel :: Map.HashMap T.Text (Path Abs File, T.Text, Int) -> T.Text -> Maybe WeakEnumCase
asEnumLabel env name = do
  case Map.lookup name env of
    Just (fp, _, _) ->
      Just $ WeakEnumCaseLabel (Just fp) name
    _ ->
      Nothing

{-# INLINE asEnumIntro #-}
asEnumIntro :: Hint -> Map.HashMap T.Text (Path Abs File, T.Text, Int) -> T.Text -> Maybe WeakTermPlus
asEnumIntro m env name = do
  case Map.lookup name env of
    Just (fp, _, _) ->
      Just (m, WeakTermEnumIntro fp name)
    _ ->
      Nothing

{-# INLINE asEnum #-}
asEnum :: Hint -> Map.HashMap T.Text (Path Abs File, a) -> T.Text -> Maybe WeakTermPlus
asEnum m env name = do
  case Map.lookup name env of
    Just (fp, _) ->
      Just (m, WeakTermEnum fp name)
    _ ->
      Nothing

-- if name `Map.member` env
--   then Just $ f name
--   else Nothing

-- {-# INLINE asMetaConstant #-}
-- asMetaConstant :: Hint -> T.Text -> Maybe MetaTermPlus
-- asMetaConstant m name =
--   if Map.member name metaConstants
--     then Just (m, MetaTermConst name)
--     else Nothing

{-# INLINE asWeakConstant #-}
asWeakConstant :: Hint -> T.Text -> Maybe WeakTermPlus
asWeakConstant m name
  | Just (LowTypeInt _) <- asLowTypeMaybe name =
    Just (m, WeakTermConst name)
  | Just (LowTypeFloat _) <- asLowTypeMaybe name =
    Just (m, WeakTermConst name)
  | Just _ <- asPrimOp name =
    Just (m, WeakTermConst name)
  | otherwise = do
    Nothing

tryCand :: (Monad m) => m (Maybe a) -> m a -> m a
tryCand comp cont = do
  mx <- comp
  case mx of
    Just x ->
      return x
    Nothing ->
      cont
