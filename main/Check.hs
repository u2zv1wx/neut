{-# LANGUAGE OverloadedStrings #-}

module Check
  ( check
  ) where

import Control.Monad.State
import Data.Binary
import Data.List (find)
import Data.Time
import Numeric
import Path
import Path.IO

import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Data.Env
import Data.Term
import Data.WeakTerm
import Elaborate
import Reduce.Term

check :: WeakStmt -> WithEnv ()
check (WeakStmtReturn e) = do
  (e', _) <- infer e
  analyze >> synthesize
  void $ elaborate e'
check (WeakStmtLet _ (_, x, t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  check' x e' t' cont
check (WeakStmtLetWT _ (_, x, t) e cont) = do
  t' <- inferType t
  check' x e t' cont
check (WeakStmtVerify m e cont) = do
  (e', _) <- infer e
  e'' <- elaborate e'
  start <- liftIO $ getCurrentTime
  _ <- normalize e''
  stop <- liftIO $ getCurrentTime
  let sec = showFloat' (realToFrac $ diffUTCTime stop start :: Float)
  note m $ "verification succeeded (" <> T.pack sec <> " seconds)"
  check cont
check (WeakStmtImplicit m x idxList cont) = do
  t <- lookupTypeEnv m (Right x) x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = Map.insertWith (++) x idxList ienv})
          check cont
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <> "` is out of range of the domain of " <> x
    _ ->
      raiseError m $
      "the type of " <>
      x <> " must be a Pi-type, but is:\n" <> toText (weaken t)
check (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> cleanup
  t'' <- reduceTermPlus <$> elaborate t'
  insTypeEnv (Right x) t''
  check cont
check (WeakStmtVisit path ss1 ss2) = do
  check ss1
  check ss2
  -- b <- isTypeCacheAvailable path
  -- cachePath <- toTypeCacheFilePath path
  -- if b
  --   then do
  --     cacheInfo <- liftIO $ decodeFile $ toFilePath cachePath
  --     withCacheInfo cacheInfo $ check ss1
  --     check ss2
  --   else do
  --     withTypeCacheAcc [] $ do
  --       check ss1
  --       acc <- gets typeCacheAcc
  --       liftIO $ encodeFile (toFilePath cachePath) acc
  --     check ss2

check' :: T.Text -> WeakTermPlus -> WeakTermPlus -> WeakStmt -> WithEnv ()
check' x e t cont
  -- met <- lookupCache x
  -- case met of
  --   Just (e', t') -> do
  --     insTypeEnv (Right x) t'
  --     modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  --     check cont
  --   Nothing -> do
 = do
  analyze >> synthesize >> cleanup
  e' <- elaborate e
  t' <- elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
      -- modify (\env -> env {typeCacheAcc = (x, (e', t')) : typeCacheAcc env})
  check cont

lookupCache :: T.Text -> WithEnv (Maybe (TermPlus, TermPlus))
lookupCache x = do
  cache <- gets typeCacheEnv
  return $ Map.lookup x cache

withTypeCacheAcc :: [(T.Text, (TermPlus, TermPlus))] -> WithEnv a -> WithEnv a
withTypeCacheAcc info f = do
  snapshot <- gets typeCacheAcc
  modify (\env -> env {typeCacheAcc = info})
  result <- f
  modify (\env -> env {typeCacheAcc = snapshot})
  return result

withCacheInfo :: [(T.Text, (TermPlus, TermPlus))] -> WithEnv a -> WithEnv a
withCacheInfo info f = do
  snapshot <- gets typeCacheEnv
  modify (\env -> env {typeCacheEnv = Map.fromList info})
  result <- f
  modify (\env -> env {typeCacheEnv = snapshot})
  return result

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = IntMap.empty})
  modify (\env -> env {zetaEnv = IntMap.empty})

showFloat' :: Float -> String
showFloat' x = showFFloat Nothing x ""

toTypeCacheFilePath :: Path Abs File -> WithEnv (Path Abs File)
toTypeCacheFilePath srcPath = do
  cacheDirPath <- getTypeCacheDirPath
  srcPath' <- parseRelFile $ "." <> toFilePath srcPath
  item <- replaceExtension ".type" $ cacheDirPath </> srcPath'
  ensureDir $ parent item
  replaceExtension ".type" $ cacheDirPath </> srcPath'

isTypeCacheAvailable :: Path Abs File -> WithEnv Bool
isTypeCacheAvailable path = do
  g <- gets depGraph
  case Map.lookup path g of
    Nothing -> isTypeCacheAvailable' path
    Just xs -> do
      b <- isTypeCacheAvailable' path
      bs <- mapM isTypeCacheAvailable xs
      return $ and $ b : bs

isTypeCacheAvailable' :: Path Abs File -> WithEnv Bool
isTypeCacheAvailable' srcPath = do
  cachePath <- toTypeCacheFilePath srcPath
  b <- doesFileExist cachePath
  if not b
    then return False
    else do
      srcModTime <- getModificationTime srcPath
      cacheModTime <- getModificationTime cachePath
      return $ srcModTime < cacheModTime
