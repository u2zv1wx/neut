{-# LANGUAGE OverloadedStrings #-}

module Build
  ( build
  ) where

import Control.Monad.State
import Data.ByteString.Builder
import Data.List (find)
import Data.Time
import Numeric
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
  llvm <- build' [] [] stmt
  p "done"
  g <- emitDeclarations
  return $ toLazyByteString $ g <> "\n" <> llvm

build' :: [Builder] -> [(Meta, T.Text, TermPlus)] -> WeakStmt -> WithEnv Builder
build' _ acc (WeakStmtReturn e) = do
  p "compiling last term"
  (e', _) <- infer e
  analyze >> synthesize >> refine
  elaborate e' >>= bind acc >>= clarify >>= toLLVM >>= emit
build' current acc (WeakStmtLet _ (mx, x, t) e cont) = do
  p "----------------------"
  p' x
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  build'' mx x current acc e' t' cont
build' current acc (WeakStmtLetWT _ (mx, x, t) e cont) = do
  p "----------------------"
  p' x
  t' <- inferType t
  build'' mx x current acc e t' cont
build' current acc (WeakStmtVerify m e cont) = do
  whenCheck $ do
    (e', _) <- infer e
    e'' <- elaborate e'
    start <- liftIO $ getCurrentTime
    _ <- normalize e''
    stop <- liftIO $ getCurrentTime
    let sec = showFloat' (realToFrac $ diffUTCTime stop start :: Float)
    note m $ "verification succeeded (" <> T.pack sec <> " seconds)"
  build' current acc cont
build' current acc (WeakStmtImplicit m x idxList cont) = do
  t <- lookupTypeEnv m (Right x) x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = Map.insertWith (++) x idxList ienv})
          build' current acc cont
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <> "` is out of range of the domain of " <> x
    _ ->
      raiseError m $
      "the type of " <>
      x <> " must be a Pi-type, but is:\n" <> toText (weaken t)
build' current acc (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- reduceTermPlus <$> elaborate t'
  insTypeEnv (Right x) t''
  build' current acc cont
build' current acc (WeakStmtBOF path cont) = do
  p $ "========BOF (" <> toFilePath path <> ")============="
  b <- isCacheAvailable path
  if b
    then do
      (cont', acc') <- bypass path cont
      modify (\env -> env {codeEnv = Map.empty})
      modify (\env -> env {llvmEnv = Map.empty})
      _ <- toCacheFilePath path
      build' current (acc' ++ acc) cont'
    else do
      build' ("" : current) acc cont
build' current acc (WeakStmtEOF path cont) = do
  p $ "========EOF (" <> toFilePath path <> ")============="
  case current of
    [] -> do
      modify (\env -> env {codeEnv = Map.empty})
      modify (\env -> env {llvmEnv = Map.empty})
      build' [] acc cont
    (code:codeList) -> do
      cachePath <- toCacheFilePath path
      tmpOutputPath <- setFileExtension "ll" cachePath
      header <- emitDeclarations
      let code' = toLazyByteString $ header <> "\n" <> code
      -- ここはspawnして最後に待つ感じにしたい
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
      modify (\env -> env {codeEnv = Map.empty})
      modify (\env -> env {llvmEnv = Map.empty})
      build' codeList acc cont -- ここでcodeをco

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

bypass ::
     Path Abs File -> WeakStmt -> WithEnv (WeakStmt, [(Meta, T.Text, TermPlus)])
bypass _ (WeakStmtReturn _) = raiseCritical' "bypass"
bypass path (WeakStmtLet _ (mx, x, t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  bypass' path mx x e' t' cont
bypass path (WeakStmtLetWT _ (mx, x, t) e cont) = do
  t' <- inferType t
  bypass' path mx x e t' cont
bypass path (WeakStmtVerify _ _ cont) = bypass path cont
bypass path (WeakStmtImplicit m x idxList cont) = do
  t <- lookupTypeEnv m (Right x) x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = Map.insertWith (++) x idxList ienv})
          bypass path cont
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <> "` is out of range of the domain of " <> x
    _ ->
      raiseError m $
      "the type of " <>
      x <> " must be a Pi-type, but is:\n" <> toText (weaken t)
bypass path (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- reduceTermPlus <$> elaborate t'
  insTypeEnv (Right x) t''
  bypass path cont
bypass path (WeakStmtBOF path' cont) = do
  p $ "========BYPASS-BOF (" <> toFilePath path' <> ")============="
  bypass path cont
bypass path (WeakStmtEOF path' cont)
  | path == path' = return (cont, [])
  | otherwise = do
    p $ "========BYPASS-EOF (" <> toFilePath path' <> ")============="
    bypass path cont

build'' ::
     Meta
  -> T.Text
  -> [Builder]
  -> [(Meta, T.Text, TermPlus)]
  -> WeakTermPlus
  -> WeakTermPlus
  -> WeakStmt
  -> WithEnv Builder
build'' mx x current acc e t cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate e
  t' <- reduceTermPlus <$> elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  llvm <- clarify e' >>= insCodeEnv (showInHex x) [] >> toLLVM' >> emit'
  cont' <- build' (concatToHead llvm current) ((mx, x, t') : acc) cont
  return $ llvm <> "\n" <> cont'

concatToHead :: Builder -> [Builder] -> [Builder]
concatToHead x [] = [x]
concatToHead x (y:ys) = (y <> "\n" <> x : ys)

bypass' ::
     Path Abs File
  -> Meta
  -> T.Text
  -> WeakTermPlus
  -> WeakTermPlus
  -> WeakStmt
  -> WithEnv (WeakStmt, [(Meta, T.Text, TermPlus)])
bypass' path mx x e t cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate e
  t' <- reduceTermPlus <$> elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  (cont', acc) <- bypass path cont
  return (cont', (mx, x, t') : acc)

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

showFloat' :: Float -> String
showFloat' x = showFFloat Nothing x ""

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})
