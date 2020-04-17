{-# LANGUAGE OverloadedStrings #-}

module Build
  ( build
  , link
  ) where

import Control.Monad.Except
import Control.Monad.State
import Data.ByteString.Builder
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

build :: WeakStmt -> WithEnv [Path Abs File]
build (WeakStmtVisit path ss1 ss2) = do
  b <- isCacheAvailable path
  if b
    then skip path ss1 >> gets cachePathList
    else do
      outputVisitHeader path
      e <- build' ss1
      modify (\env -> env {argAcc = []})
      mainTerm <- build' ss2 >>= letBind e
      clarify mainTerm >>= toLLVM >>= emit >>= compileObject path
      gets cachePathList
build _ = raiseCritical' "build"

link :: Path Abs File -> [Path Abs File] -> [String] -> IO ()
link outputPath pathList opt = do
  callProcess "clang" $
    map toFilePath pathList ++
    opt ++ ["-Wno-override-module", "-o" ++ toFilePath outputPath]

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
  b <- isCacheAvailable path
  if b
    then skip path ss1 >> build' ss2
    else do
      outputVisitHeader path
      e <-
        withStack $ do
          e <- build' ss1
          toLLVM' >> emit' >>= compileObject path
          return e
      build' ss2 >>= letBind e

skip :: Path Abs File -> WeakStmt -> WithEnv ()
skip path ss = do
  outputSkipHeader path
  bypass ss
  toCacheFilePath path >>= insCachePath

letBind :: TermPlus -> TermPlus -> WithEnv TermPlus
letBind e cont = do
  h <- newNameWith'' "_"
  let m = fst e
  let intType = (m, TermEnum (EnumTypeIntS 64))
  return (m, TermPiElim (m, termPiIntro [(m, h, intType)] cont) [e])

outputVisitHeader :: Path Abs File -> WithEnv ()
outputVisitHeader path = do
  i <- gets nestLevel
  note' $ T.replicate (i * 2) " " <> "→ " <> T.pack (toFilePath path)

outputSkipHeader :: Path Abs File -> WithEnv ()
outputSkipHeader path = do
  i <- gets nestLevel
  note' $ T.replicate (i * 2) " " <> "✓ " <> T.pack (toFilePath path)

withStack :: WithEnv a -> WithEnv a
withStack f = do
  snapshot <- setupEnv
  result <- f
  revertEnv snapshot
  return result

setupEnv :: WithEnv Env
setupEnv = do
  snapshot <- get
  modify (\env -> env {nestLevel = (nestLevel env) + 1})
  modify (\env -> env {codeEnv = Map.empty})
  modify (\env -> env {llvmEnv = Map.empty})
  modify (\env -> env {argAcc = []})
  return snapshot

revertEnv :: Env -> WithEnv ()
revertEnv snapshot = do
  modify (\env -> env {nestLevel = (nestLevel env) - 1})
  modify (\e -> e {codeEnv = codeEnv snapshot})
  modify (\e -> e {llvmEnv = llvmEnv snapshot})
  modify (\e -> e {argAcc = argAcc snapshot})

compileObject :: Path Abs File -> Builder -> WithEnv ()
compileObject srcPath code = do
  cachePath <- toCacheFilePath srcPath
  tmpOutputPath <- replaceExtension ".ll" cachePath
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
build'' mx x e t cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate e
  t' <- reduceTermPlus <$> elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  clarify e' >>= insCodeEnv (showInHex x) []
  modify (\env -> env {argAcc = (mx, x, t') : (argAcc env)})
  build' cont

bypass :: WeakStmt -> WithEnv ()
bypass (WeakStmtReturn _) = return ()
bypass (WeakStmtLet _ (_, x, t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  bypass' x e' t' cont
bypass (WeakStmtLetWT _ (_, x, t) e cont) = do
  t' <- inferType t
  bypass' x e t' cont
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
bypass (WeakStmtVisit path ss1 ss2) = do
  cachePath <- toCacheFilePath path
  insCachePath cachePath
  bypass ss1
  bypass ss2

bypass' :: T.Text -> WeakTermPlus -> WeakTermPlus -> WeakStmt -> WithEnv ()
bypass' x e t cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate e
  t' <- reduceTermPlus <$> elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  bypass cont

bind :: [(Meta, T.Text, TermPlus)] -> TermPlus -> WithEnv TermPlus
bind [] e = return e
bind ((m, c, t):cts) e = do
  h <- newNameWith'' "_"
  bind cts (m, TermPiElim (m, termPiIntro [(m, h, t)] e) [(m, TermConst c)])

cleanup :: WithEnv ()
cleanup = do
  modify (\env -> env {constraintEnv = []})
  modify (\env -> env {weakTypeEnv = IntMap.empty})
  modify (\env -> env {zetaEnv = IntMap.empty})

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})
