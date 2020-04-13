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
  llvm <- build' [] stmt
  p "done"
  g <- emitDeclarations
  return $ toLazyByteString $ g <> "\n" <> llvm

build' :: [(Meta, T.Text, TermPlus)] -> WeakStmt -> WithEnv Builder
build' acc (WeakStmtReturn e) = do
  p "compiling last term"
  (e', _) <- infer e
  analyze >> synthesize >> refine
  elaborate e' >>= bind acc >>= clarify >>= toLLVM >>= emit
build' acc (WeakStmtLet _ (mx, x, t) e cont) = do
  p "----------------------"
  p' x
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  build'' mx x acc e' t' cont
build' acc (WeakStmtLetWT _ (mx, x, t) e cont) = do
  p "----------------------"
  p' x
  t' <- inferType t
  build'' mx x acc e t' cont
build' acc (WeakStmtVerify m e cont) = do
  whenCheck $ do
    (e', _) <- infer e
    e'' <- elaborate e'
    start <- liftIO $ getCurrentTime
    _ <- normalize e''
    stop <- liftIO $ getCurrentTime
    let sec = showFloat' (realToFrac $ diffUTCTime stop start :: Float)
    note m $ "verification succeeded (" <> T.pack sec <> " seconds)"
  build' acc cont
build' acc (WeakStmtImplicit m x idxList cont) = do
  t <- lookupTypeEnv m (Right x) x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = Map.insertWith (++) x idxList ienv})
          build' acc cont
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <> "` is out of range of the domain of " <> x
    _ ->
      raiseError m $
      "the type of " <>
      x <> " must be a Pi-type, but is:\n" <> toText (weaken t)
build' acc (WeakStmtConstDecl _ (_, x, t) cont) = do
  t' <- inferType t
  analyze >> synthesize >> refine >> cleanup
  t'' <- reduceTermPlus <$> elaborate t'
  insTypeEnv (Right x) t''
  build' acc cont
build' acc (WeakStmtVisit path ss1 ss2) = do
  p $ "========VISIT (" <> toFilePath path <> ")============="
  b <- isCacheAvailable path
  if b
    then do
      acc' <- bypass ss1 -- 引数情報だけ集める
      cachePath <- toCacheFilePath path
      code <- readCache cachePath
      cont <- build' (acc' ++ acc) ss2
      return $ code <> cont
    else do
      cenv <- gets codeEnv
      -- ss1をcodeEnv = emptyとしてwithEnvで実行してどうにかする
      undefined

readCache :: Path Abs File -> WithEnv Builder
readCache = undefined

-- build' acc (WeakStmtBOF path cont) = do
--   p $ "========BOF (" <> toFilePath path <> ")============="
--   b <- isCacheAvailable path
--   if b
--     then do
--       (cont', acc') <- bypass path cont
--       modify (\env -> env {codeEnv = Map.empty})
--       modify (\env -> env {llvmEnv = Map.empty})
--       _ <- toCacheFilePath path
--       build' (acc' ++ acc) cont'
--     else do
--       build' acc cont -- ここでevalWithEnvでcodeEnv = emptyでrunするのが正解っぽい？
--       -- そうすると全てのファイルがmain fileであるかのように扱われることになる？
--       -- 現在注目中のpathのEOFが出てくるまで続ける、みたいな？
--       -- それ結局Stmtのほうにネスト構造を反映させろって話にならない？
--       -- つまりWeakStmtOtherFile Stmt Stmtみたいな感じで。
--       -- 第1引数のほうもreturnで終了するわけだけど、ここがEOFに対応する、と。
--       -- それ、たとえばcheckのほうはどうなる？前のstmtを全部チェックしてから後ろのStmtをチェックするだけか。
--       -- このときはそれぞれのファイルの末尾にreturn 0が入ってるって理解になるわけですね。
-- build' _ (WeakStmtEOF path (WeakStmtReturn _)) = do
--   p $ "========LAST-EOF (" <> toFilePath path <> ")============="
--   error "stop"
-- build' acc (WeakStmtEOF path cont) = do
--   p $ "========EOF (" <> toFilePath path <> ")============="
--   cachePath <- toCacheFilePath path
--   tmpOutputPath <- setFileExtension "ll" cachePath
--   code <- toLLVM' >> emit'
--   header <- emitDeclarations
--   let code' = toLazyByteString $ header <> "\n" <> code
--   liftIO $ L.writeFile (toFilePath tmpOutputPath) code'
--   liftIO $
--     callProcess
--       "clang"
--       [ "-c"
--       , toFilePath tmpOutputPath
--       , "-Wno-override-module"
--       , "-o" ++ toFilePath cachePath
--       ]
--   removeFile tmpOutputPath
--   -- sharedCodeEnvは保持
--   modify (\env -> env {codeEnv = Map.empty}) -- ここは修正必要？
--   modify (\env -> env {llvmEnv = Map.empty})
--   build' acc cont
build'' ::
     Meta
  -> T.Text
  -> [(Meta, T.Text, TermPlus)]
  -> WeakTermPlus
  -> WeakTermPlus
  -> WeakStmt
  -> WithEnv Builder
build'' mx x acc e t cont = do
  analyze >> synthesize >> refine >> cleanup
  e' <- reduceTermPlus <$> elaborate e
  t' <- reduceTermPlus <$> elaborate t
  insTypeEnv (Right x) t'
  modify (\env -> env {cacheEnv = Map.insert x (Left e') (cacheEnv env)})
  clarify e' >>= insCodeEnv (showInHex x) []
  build' ((mx, x, t') : acc) cont

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
  t <- lookupTypeEnv m (Right x) x
  case t of
    (_, TermPi _ xts _) -> do
      case find (\idx -> idx < 0 || length xts <= idx) idxList of
        Nothing -> do
          ienv <- gets impEnv
          modify (\env -> env {impEnv = Map.insertWith (++) x idxList ienv})
          bypass cont
        Just idx -> do
          raiseError m $
            "the specified index `" <>
            T.pack (show idx) <> "` is out of range of the domain of " <> x
    _ ->
      raiseError m $
      "the type of " <>
      x <> " must be a Pi-type, but is:\n" <> toText (weaken t)
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

showFloat' :: Float -> String
showFloat' x = showFFloat Nothing x ""

refine :: WithEnv ()
refine =
  modify (\env -> env {substEnv = IntMap.map reduceWeakTermPlus (substEnv env)})
