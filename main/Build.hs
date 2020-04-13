{-# LANGUAGE OverloadedStrings #-}

module Build
  ( build
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

build :: WeakStmt -> WithEnv L.ByteString
build stmt = do
  llvm <- build' stmt
  g <- emitDeclarations
  return $ toLazyByteString $ g <> "\n" <> llvm

build' :: WeakStmt -> WithEnv Builder
build' (WeakStmtReturn e) = do
  (e', _) <- infer e
  analyze >> synthesize >> refine
  acc <- gets argAcc
  elaborate e' >>= bind acc >>= clarify >>= toLLVM >>= emit
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
  p $ "========VISIT (" <> toFilePath path <> ")============="
  b <- isCacheAvailable path
  if b
    then do
      acc' <- bypass ss1 -- 引数情報だけ集める (clarify/toLLVM/emitをbypass)
      modify (\env -> env {argAcc = acc' ++ (argAcc env)})
      cachePath <- toCacheFilePath path
      code <- undefined cachePath
      insCachePath cachePath
      cont <- build' ss2
      -- ここのcodeはfoo.oじゃなくてfoo.llじゃないとダメでは？
      return $ code <> cont
    else do
      env1 <- get
      let env1' = env1 {codeEnv = Map.empty, llvmEnv = Map.empty}
      resultOrErr <- liftIO $ runWithEnv (build' ss1) env1'
      case resultOrErr of
        Left err -> throwError err
        Right (code, env2) -> do
          compileObject path code
          updateEnv env1 env2
          cont <- build' ss2
          return $ code <> cont

updateEnv :: Env -> Env -> WithEnv ()
updateEnv oldEnv newEnv = do
  let sc1 = sharedCodeEnv oldEnv
  let sc2 = sharedCodeEnv newEnv
  modify (\e -> e {codeEnv = Map.union (codeEnv oldEnv) (codeEnv newEnv)})
  modify (\e -> e {llvmEnv = Map.union (llvmEnv oldEnv) (llvmEnv newEnv)})
  modify (\e -> e {sharedCodeEnv = Map.union sc1 sc2})

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
  -> WithEnv Builder
build'' mx x e t cont = do
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
