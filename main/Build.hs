{-# LANGUAGE OverloadedStrings #-}

module Build
  ( build
  , link
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.ByteString.Builder
import Data.List (find)
import Path
import Path.IO
import System.Process (callProcess)

import qualified Data.ByteString.Lazy as L
import qualified Data.HashMap.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Text as T

import Clarify
import Data.Basic
import Data.Env
import Data.Term
import Data.WeakTerm
import Elaborate
import Emit
import LLVM
import Reduce.Term
import Reduce.WeakTerm

build :: Path Abs File -> WeakStmt -> WithEnv [Path Abs File]
build _ (WeakStmtVisit path ss1 retZero)
  -- note' $ "→ visit: " <> T.pack (toFilePath path)
 = do
  e <- build' ss1
  retZero' <- build' retZero
  mainTerm <- letBind e retZero'
  llvm <- clarify mainTerm >>= toLLVM >>= emit -- main termのビルドはココで行う。
  sharedCode <- buildShared
  -- note' $ "← compile: " <> T.pack (toFilePath path)
  compileObject path $ sharedCode <> "\n" <> llvm
  gets cachePathList
build _ _ = undefined
  -- note' $ "→ visit: " <> T.pack (toFilePath mainFilePath)
  -- e <- build' stmt
  -- llvm <- clarify e >>= toLLVM >>= emit -- main termのビルドはココで行う。
  -- sharedCode <- buildShared
  -- note' $ "← compile: " <> T.pack (toFilePath mainFilePath)
  -- compileObject mainFilePath $ sharedCode <> "\n" <> llvm
  -- gets cachePathList

link :: Path Abs File -> [Path Abs File] -> IO ()
link outputPath pathList = do
  callProcess "clang" $
    map toFilePath pathList ++
    ["-Wno-override-module", "-o" ++ toFilePath outputPath]

build' :: WeakStmt -> WithEnv TermPlus
build' (WeakStmtReturn e) = do
  (e', _) <- infer e
  analyze >> synthesize >> refine
  acc <- gets argAcc
  elaborate e' >>= bind acc
build' (WeakStmtLet _ (mx, x, t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  build'' mx x e' t' cont
build' (WeakStmtLetWT _ (mx, x, t) e cont) = do
  t' <- inferType t
  build'' mx x e t' cont
build' (WeakStmtVerify _ _ cont) = build' cont
build' (WeakStmtImplicit m x idxList cont) = do
  resolveImplicit m x idxList
  build' cont
build' (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- reduceTermPlus <$> elaborate t'
  insTypeEnv (Right x) t''
  build' cont
build' (WeakStmtVisit path ss1 ss2) = do
  note' $ "→ visit: " <> T.pack (toFilePath path)
  b <- isCacheAvailable path
  if b
    then do
      note' $ "← using cache for " <> T.pack (toFilePath path)
      acc' <- bypass ss1
      modify (\env -> env {argAcc = acc' ++ (argAcc env)})
      cachePath <- toCacheFilePath path
      insCachePath cachePath
      build' ss2
    else do
      snapshot <- setupEnv
      e <- build' ss1
      toLLVM'
      code <- emit'
      note' $ "← compile: " <> T.pack (toFilePath path)
      compileObject path code -- オブジェクトファイルを構成
      revertEnv snapshot
      cont <- build' ss2 -- このcontの結果もあくまでLLVM IR
      letBind e cont

letBind :: TermPlus -> TermPlus -> WithEnv TermPlus
letBind e cont = do
  h <- newNameWith'' "_"
  let m = fst e
  let intType = (m, TermEnum (EnumTypeIntS 64))
  return (m, TermPiElim (m, TermPiIntro [(m, h, intType)] cont) [e])

setupEnv :: WithEnv Env
setupEnv = do
  snapshot <- get
  modify (\env -> env {codeEnv = Map.empty})
  modify (\env -> env {llvmEnv = Map.empty})
  modify (\env -> env {argAcc = []})
  return snapshot

revertEnv :: Env -> WithEnv ()
revertEnv snapshot = do
  modify (\e -> e {codeEnv = codeEnv snapshot})
  modify (\e -> e {llvmEnv = llvmEnv snapshot})
  -- modify (\e -> e {declEnv = declEnv snapshot})
  modify (\e -> e {argAcc = argAcc snapshot})

buildShared :: WithEnv Builder
buildShared = do
  scenv <- gets sharedCodeEnv
  modify (\env -> env {codeEnv = scenv, llvmEnv = Map.empty})
  denv <- gets declEnv
  let denv' = Map.filterWithKey (\k _ -> not $ Map.member k scenv) denv
  modify (\env -> env {declEnv = denv'})
  toLLVM'
  emit'

compileObject :: Path Abs File -> Builder -> WithEnv ()
compileObject srcPath code = do
  cachePath <- toCacheFilePath srcPath
  tmpOutputPath <- setFileExtension "ll" cachePath
  header <- emitDeclarations
  let code' = toLazyByteString $ header <> "\n" <> code
  liftIO $ L.writeFile (toFilePath tmpOutputPath) code'
  liftIO $
    callProcess
      "clang"
      [ "-c"
      , toFilePath tmpOutputPath
      , "-Wno-override-module"
      , "-o" ++ toFilePath cachePath
      ]
  removeFile tmpOutputPath
  insCachePath cachePath

insCachePath :: Path Abs File -> WithEnv ()
insCachePath path =
  modify (\env -> env {cachePathList = path : (cachePathList env)})

build'' ::
     Meta
  -> T.Text
  -> WeakTermPlus
  -> WeakTermPlus
  -> WeakStmt
  -> WithEnv TermPlus
build'' mx x e t cont
  -- p' x
 = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate e
  t' <- reduceTermPlus <$> elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  clarify e' >>= insCodeEnv (showInHex x) []
  modify (\env -> env {argAcc = (mx, x, t') : (argAcc env)})
  build' cont

-- 当該pathから計算されるパスにキャッシュが存在して、かつそのキャッシュのlast modifiedがソースファイルの
-- last modifiedよりも新しければcache利用可能。（依存関係も計算）
isCacheAvailable :: Path Abs File -> WithEnv Bool
isCacheAvailable _ = return False

toCacheFilePath :: Path Abs File -> WithEnv (Path Abs File)
toCacheFilePath srcPath = do
  cacheDirPath <- getObjectCacheDirPath
  srcPath' <- parseRelFile $ "." <> toFilePath srcPath
  item <- setFileExtension "o" $ cacheDirPath </> srcPath'
  ensureDir $ parent item
  setFileExtension "o" $ cacheDirPath </> srcPath'

bypass :: WeakStmt -> WithEnv [(Meta, T.Text, TermPlus)]
bypass (WeakStmtReturn _) = return []
bypass (WeakStmtLet _ (mx, x, t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  bypass' mx x e' t' cont
bypass (WeakStmtLetWT _ (mx, x, t) e cont) = do
  t' <- inferType t
  bypass' mx x e t' cont
bypass (WeakStmtVerify _ _ cont) = bypass cont
bypass (WeakStmtImplicit m x idxList cont) = do
  resolveImplicit m x idxList
  bypass cont
bypass (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- reduceTermPlus <$> elaborate t'
  insTypeEnv (Right x) t''
  bypass cont
bypass (WeakStmtVisit _ ss1 ss2) = do
  acc1 <- bypass ss1
  acc2 <- bypass ss2
  return $ acc1 ++ acc2

bypass' ::
     Meta
  -> T.Text
  -> WeakTermPlus
  -> WeakTermPlus
  -> WeakStmt
  -> WithEnv [(Meta, T.Text, TermPlus)]
bypass' mx x e t cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate e
  t' <- reduceTermPlus <$> elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  acc <- bypass cont
  return $ (mx, x, t') : acc

bind :: [(Meta, T.Text, TermPlus)] -> TermPlus -> WithEnv TermPlus
bind [] e = return e
bind ((m, c, t):cts) e = do
  h <- newNameWith'' "_"
  bind cts (m, TermPiElim (m, TermPiIntro [(m, h, t)] e) [(m, TermConst c)])

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = IntMap.empty})
  modify (\env -> env {zetaEnv = IntMap.empty})

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})

resolveImplicit :: Meta -> T.Text -> [Int] -> WithEnv ()
resolveImplicit m x idxList = do
  t <- lookupTypeEnv m (Right x) x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = Map.insertWith (++) x idxList ienv})
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <> "` is out of range of the domain of " <> x
    _ ->
      raiseError m $
      "the type of " <>
      x <> " must be a Pi-type, but is:\n" <> toText (weaken t)
