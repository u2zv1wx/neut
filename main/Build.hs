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

build :: WeakStmt -> WithEnv [Path Abs File]
build (WeakStmtVisit path ss1 retZero) = do
  b <- isCacheAvailable path
  if b
    then do
      note' $ "✓ " <> T.pack (toFilePath path)
      bypass ss1
      cachePath <- toCacheFilePath path
      insCachePath cachePath
      gets cachePathList
    else do
      note' $ "→ " <> T.pack (toFilePath path)
      modify (\env -> env {nestLevel = nestLevel env + 1})
      e <- build' ss1
      modify (\env -> env {argAcc = []})
      retZero' <- build' retZero
      mainTerm <- letBind e retZero'
      llvm <- clarify mainTerm >>= toLLVM >>= emit
      compileObject path llvm
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
  i <- gets nestLevel
  if b
    then do
      note' $ T.replicate (i * 2) " " <> "✓ " <> T.pack (toFilePath path)
      bypass ss1
      cachePath <- toCacheFilePath path
      insCachePath cachePath
      build' ss2
    else do
      note' $ T.replicate (i * 2) " " <> "→ " <> T.pack (toFilePath path)
      modify (\env -> env {nestLevel = i + 1})
      snapshot <- setupEnv
      e <- build' ss1
      code <- toLLVM' >> emit'
      modify (\env -> env {nestLevel = i})
      compileObject path code
      revertEnv snapshot
      cont <- build' ss2
      letBind e cont

letBind :: TermPlus -> TermPlus -> WithEnv TermPlus
letBind e cont = do
  h <- newNameWith'' "_"
  let m = fst e
  let intType = (m, TermEnum (EnumTypeIntS 64))
  return (m, TermPiElim (m, termPiIntro [(m, h, intType)] cont) [e])

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

isCacheAvailable :: Path Abs File -> WithEnv Bool
isCacheAvailable path = do
  g <- gets depGraph
  case Map.lookup path g of
    Nothing -> isCacheAvailable' path
    Just xs -> do
      b <- isCacheAvailable' path
      bs <- mapM isCacheAvailable xs
      return $ and $ b : bs

isCacheAvailable' :: Path Abs File -> WithEnv Bool
isCacheAvailable' srcPath = do
  cachePath <- toCacheFilePath srcPath
  b <- doesFileExist cachePath
  if not b
    then return False
    else do
      srcModTime <- getModificationTime srcPath
      cacheModTime <- getModificationTime cachePath
      return $ srcModTime < cacheModTime

toCacheFilePath :: Path Abs File -> WithEnv (Path Abs File)
toCacheFilePath srcPath = do
  cacheDirPath <- getObjectCacheDirPath
  srcPath' <- parseRelFile $ "." <> toFilePath srcPath
  item <- replaceExtension ".o" $ cacheDirPath </> srcPath'
  ensureDir $ parent item
  replaceExtension ".o" $ cacheDirPath </> srcPath'

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
