{-# LANGUAGE OverloadedStrings #-}

module Build
  ( build
  ) where

import Control.Monad.State
import Data.ByteString.Builder
import Data.List (find)
import Data.Time
import Numeric

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
  g <- emitDeclarations
  return $ toLazyByteString $ g <> "\n" <> llvm

build' :: [(Meta, T.Text, TermPlus)] -> WeakStmt -> WithEnv Builder
build' acc (WeakStmtReturn e) = do
  (e', _) <- infer e
  analyze >> synthesize >> refine
  elaborate e' >>= bind acc >>= clarify >>= toLLVM >>= emit
build' acc (WeakStmtLet _ (mx, x, t) e cont) = do
  (e', te) <- infer e
  t' <- inferType t
  insConstraintEnv te t'
  build'' mx x acc e' t' cont
build' acc (WeakStmtLetWT _ (mx, x, t) e cont) = do
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
  llvm <- clarify e' >>= insCodeEnv (showInHex x) [] >> toLLVM' >> emit'
  cont' <- build' ((mx, x, t') : acc) cont
  return $ llvm <> "\n" <> cont'

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
